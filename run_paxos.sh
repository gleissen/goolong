#!/bin/zsh

blue()  { print -P "%F{blue}%B$1%b%f" }
green() { print -P "%F{green}%B$1%b%f" }
red()   { print -P "%F{red}%B$1%b%f" }

# trap CTRL-C input, and kill every process created
trap "pkill -P $$; sleep 1; exit 1;" INT

t=4

blue "running eval ..."

ADDR="127.0.0.1"

ADDRS=( "$ADDR:7070" "$ADDR:7071" "$ADDR:7072" )

bin/multipaxos -b -addr "$ADDR:7070" -id 0 -log "log0" ${ADDRS[@]} &
bin/multipaxos -b -addr "$ADDR:7071" -id 1 -log "log1" ${ADDRS[@]} &
bin/multipaxos -b -addr "$ADDR:7072" -id 2 -log "log2" ${ADDRS[@]} &

blue "sleeping for $t seconds ..."
sleep $((t + 2))

blue "stopping ..."
pkill -P $$
sleep 1

