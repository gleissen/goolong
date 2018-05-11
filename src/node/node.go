package node

import "fmt"
import "log"
import "net"
import "time"
import "encoding/binary"
import "bufio"
import "io"
import "fastrpc"

const CHAN_BUFFER_SIZE = 200000

type RPCPair struct {
	Obj   fastrpc.Serializable
	Chans []chan fastrpc.Serializable
}

type Node struct {
	Id        int
	N         int // number of connections
	IsServer  bool
	AddrList  []string // array with the IP:port addresses
	MyAddr    string
	Peers     []net.Conn // cache of connections to all other nodes
	PeerIds   []int
	Listener  net.Listener
	Readers   []*bufio.Reader
	Writers   []*bufio.Writer
	Connected chan bool
	Done      chan bool
	rpcTable  map[uint8]*RPCPair
	rpcCode   uint8
}

func MakeNode(id int, myaddr string, peerAddrList []string, isServer bool) *Node {
	N := len(peerAddrList)
	peerIds := makePeerIds(N)
	n := &Node{
		id,
		N,
		isServer,
		peerAddrList,
		myaddr,
		make([]net.Conn, N),
		peerIds,
		nil,
		make([]*bufio.Reader, N),
		make([]*bufio.Writer, N),
		make(chan bool, 1),
		make(chan bool, 1),
		make(map[uint8]*RPCPair),
		0}
	return n
}

func makePeerIds(N int) []int {
	ids := make([]int, N)
	for i := range ids {
		ids[i] = i
	}
	return ids
}

// Connect to peers
func (n *Node) Connect() {
	if !n.IsServer {
		n.waitForConnections() //(done)
	} else {
		var b [4]byte
		bs := b[:4]
		//connect to peers
		for i := 0; i < n.N; i++ {
			for done := false; !done; {
				if conn, err := net.Dial("tcp", n.AddrList[i]); err == nil {
					n.Peers[i] = conn
					done = true
				} else {
					time.Sleep(1e9)
				}
			}
			binary.LittleEndian.PutUint32(bs, uint32(n.Id))
			if _, err := n.Peers[i].Write(bs); err != nil {
				fmt.Println("Write id error:", err)
				continue
			}
			n.Readers[i] = bufio.NewReader(n.Peers[i])
			n.Writers[i] = bufio.NewWriter(n.Peers[i])
		}
	}
	//<-done
	log.Printf("Replica id: %d. Done connecting.\n", n.Id)
	n.Connected <- true
	// listen for messages from each peer node
	for rid, reader := range n.Readers {
		go n.msgListener(rid, reader)
	}
}

/* Connection dispatcher */
func (n *Node) waitForConnections() { //done chan bool) {
	var b [4]byte
	bs := b[:4]
	fmt.Printf("waiting for peer connections at address %v\n", n.MyAddr)
	n.Listener, _ = net.Listen("tcp", n.MyAddr)
	for i := 0; i < n.N; i++ {
		conn, err := n.Listener.Accept()
		fmt.Printf("connection from %vth peer \n", i)
		if err != nil {
			fmt.Println("Accept error:", err)
			continue
		}
		if _, err := io.ReadFull(conn, bs); err != nil {
			fmt.Println("Connection error:", err)
			continue
		}
		id := int32(binary.LittleEndian.Uint32(bs))
		fmt.Println("Connection established for replica:", id)
		n.Peers[i] = conn
		n.Readers[i] = bufio.NewReader(conn)
		n.Writers[i] = bufio.NewWriter(conn)
	}
	//done <- true
	fmt.Printf("Replica id: %d. Done connecting to peers\n", n.Id)
}

func (n *Node) msgListener(id int, reader *bufio.Reader) {
	for {
		// loop until we get a done messsage
		select {
		case <-n.Done:
			break
		default:
			// read a byte containing the message type
			msgType, err := reader.ReadByte()
			if err != nil {
				break
			}
			thisRpc := n.rpcTable[msgType]
			obj := thisRpc.Obj.New()
			if err := obj.Unmarshal(reader); err != nil {
				break
			}
			thisRpc.Chans[id] <- obj
		}
	}
}

func (n *Node) RegisterRPC(msgObj fastrpc.Serializable, chans []chan fastrpc.Serializable) uint8 {
	code := n.rpcCode
	n.rpcCode++
	n.rpcTable[code] = &RPCPair{Obj: msgObj, Chans: chans}
	return code
}

func (n *Node) NSend(id int, code uint8, msg fastrpc.Serializable) {
	wire := n.Writers[id]
	wire.WriteByte(code)
	msg.Marshal(wire)
	wire.Flush()
}

func (n *Node) Run() {
	n.Connect()
}
