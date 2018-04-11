package main

import "gochai"

func main() {
	gochai.Send(1, 2)
	gochai.Recv(2, 1)
}
