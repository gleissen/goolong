package main

import (
	"bufio"
	"clientproto"
	"dlog"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"net"
	"state"
	"time"
)

var rounds *int = flag.Int("r", 1, "Split the total number of requests into this many rounds, and do rounds sequentially. Defaults to 1.")
var reqsNb *int = flag.Int("q", 5000, "Total number of requests. Defaults to 5000.")
var writes *int = flag.Int("w", 100, "Percentage of updates (writes). Defaults to 100%.")
var conflicts *int = flag.Int("c", -1, "Percentage of conflicts. Defaults to 0%")

var N int
var successful []int

func main() {
	flag.Parse()
	replicaList := flag.Args()
	if *conflicts > 100 {
		log.Fatalf("Conflicts percentage must be between 0 and 100.\n")
	}

	put := make([]bool, *reqsNb)
	karray := make([]int64, *reqsNb)

	// building workload
	for i := 0; i < len(karray); i++ {
		r := rand.Intn(100)
		if r < *conflicts {
			karray[i] = 42
		} else {
			karray[i] = int64(43 + i)
		}
		r = rand.Intn(100)
		if r < *writes {
			put[i] = true
		} else {
			put[i] = false
		}

		//connecting to servers
		servers := make([]net.Conn, N)
		readers := make([]*bufio.Reader, N)
		writers := make([]*bufio.Writer, N)
		for i := 0; i < N; i++ {
			var err error
			servers[i], err = net.Dial("tcp", replicaList[i])
			if err != nil {
				log.Printf("Error connecting to replica %d\n", i)
			}
			readers[i] = bufio.NewReader(servers[i])
			writers[i] = bufio.NewWriter(servers[i])
		}

		successful := make([]int, N)
		leader := 0
		done := make(chan bool, N)
		var id int32 = 0
		args := clientproto.Propose{CommandId: id, Command: state.Command{Op: state.PUT, K: 0, V: 0}}
		before_total := time.Now()
		// sending requests
		for j := 0; j < *rounds; j++ {

			n := *reqsNb / *rounds
			for i := 0; i < n; i++ {

				before := time.Now()
				go waitReplies(readers, leader, n, done)
				dlog.Printf("Sending proposal %d\n", id)
				args.CommandId = id
				if put[i] {
					args.Command.Op = state.PUT
				} else {
					args.Command.Op = state.GET
				}
				args.Command.K = state.Key(karray[i])
				args.Command.V = state.Value(i)

				for rep := 0; rep < N; rep++ {
					writers[rep].WriteByte(clientproto.PROPOSE)
					args.Marshal(writers[rep])
					writers[rep].Flush()
				}
				for i := 0; i < N; i++ {
					writers[i].Flush()
				}
				err := <-done
				after := time.Now()
				fmt.Printf("Round took %v\n", after.Sub(before))
				if err {
					leader = (leader + 1) % N
				}
				id++
			}
		}
		after_total := time.Now()
		fmt.Printf("Test took %v\n", after_total.Sub(before_total))
		s := 0
		for _, succ := range successful {
			s += succ
		}

		fmt.Printf("Successful: %d\n", s)
	}
}

func waitReplies(readers []*bufio.Reader, leader int, n int, done chan bool) {
	e := false

	reply := new(clientproto.ProposeReply)
	for i := 0; i < n; i++ {
		if err := reply.Unmarshal(readers[leader]); err != nil {
			fmt.Println("Error when reading:", err)
			e = true
			continue
		}
		if reply.OK != 0 {
			successful[leader]++
		}
	}
	done <- e
}
