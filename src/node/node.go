package node

import "fmt"
import "log"
import "net"
import "time"
import "encoding/binary"
import "bufio"
import "io"

const CHAN_BUFFER_SIZE = 200000

type Node struct {
	Id       int
	N        int      // number of connections
	AddrList []string // array with the IP:port addresses
	MyAddr   string
	Peers    []net.Conn // cache of connections to all other nodes
	Listener net.Listener
	Readers  []*bufio.Reader
	Writers  []*bufio.Writer
	MsgChan  chan int32
}

func MakeNode(id int, myaddr string, peerAddrList []string) *Node {
	n := &Node{
		id,
		len(peerAddrList),
		peerAddrList,
		myaddr,
		make([]net.Conn, len(peerAddrList)),
		nil,
		make([]*bufio.Reader, len(peerAddrList)),
		make([]*bufio.Writer, len(peerAddrList)),
		make(chan int32, CHAN_BUFFER_SIZE)}
	return n
}

func (n *Node) Connect(connected chan bool) {
	done := make(chan bool)
	var b [4]byte
	bs := b[:4]
	go n.waitForConnections(done)
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
	<-done
	log.Printf("Replica id: %d. Done connecting.\n", n.Id)
	connected <- true
	// listen for messages from each peer node
	for rid, reader := range n.Readers {
		go n.msgListener(rid, reader)
	}
}

/* Connection dispatcher */
func (n *Node) waitForConnections(done chan bool) {
	var b [4]byte
	bs := b[:4]
	fmt.Printf("waiting for connections at address %v\n", n.MyAddr)
	n.Listener, _ = net.Listen("tcp", n.MyAddr)
	for i := 0; i < n.N; i++ {
		fmt.Printf("waiting for connections from %v\n", i)
		conn, err := n.Listener.Accept()
		fmt.Printf("established\n")
		if err != nil {
			fmt.Println("Accept error:", err)
			continue
		}
		if _, err := io.ReadFull(conn, bs); err != nil {
			fmt.Println("Connection establish error:", err)
			continue
		}
		id := int32(binary.LittleEndian.Uint32(bs))
		fmt.Println("Connection establish for replica:", id)
		n.Peers[i] = conn
		n.Readers[i] = bufio.NewReader(conn)
		n.Writers[i] = bufio.NewWriter(conn)
	}
	done <- true
	fmt.Printf("Replica id: %d. Done connecting to peers\n", n.Id)
}

func (n *Node) msgListener(id int, reader *bufio.Reader) {
	var b [4]byte
	bs := b[:4]
	if _, err := io.ReadAtLeast(reader, bs, 4); err != nil {
		log.Printf("Error reading message from %v", id)
	}
	msg := int32(binary.LittleEndian.Uint32(bs))
	n.MsgChan <- msg
}

func (n *Node) Send(id int, msg int32) {
	var b [4]byte
	bs := b[:4]
	w := n.Writers[id]
	binary.LittleEndian.PutUint32(bs, uint32(msg))
	w.Write(bs)
	w.Flush()
}

func (n *Node) Run(connected chan bool) {
	n.Connect(connected)
}
