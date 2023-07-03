package main

import (
	"fmt"
	"os"
	"os/user"
	"wiig/repl"
)

func main() {
	user, err := user.Current()
	if err != nil {
		panic(err)
	}
	fmt.Printf("Hello %s this is the Monkey programming language!\n", user.Username)
	fmt.Printf("Type a command\n")
	repl.Start(os.Stdin, os.Stdout)
}
