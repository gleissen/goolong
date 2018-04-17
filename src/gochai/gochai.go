package gochai

import "fmt"

// sending a value
func Send(addr int, msg int) {
	fmt.Printf("send %v to %v\n", addr, msg)
}

// receiving a value
func Recv(addr int, msg int) {
	fmt.Printf("recv %v from %v\n", addr, msg)
}

// TODO
func Broadcast(addr []int, msg int) {
	//TODO
	fmt.Printf("send %v to %v\n", addr, msg)

}
