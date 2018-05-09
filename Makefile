THIS_DIR   = $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
GO         = env GOPATH="$(THIS_DIR)" go
GO_INSTALL = $(GO) install
BIN_DIR    = $(THIS_DIR)/bin

BINARIES   = bin/twopc bin/icet
COMMANDS   = twopc-coord twopc-db1 twopc-db2 \
			 twopc-icet

.PHONY: $(COMMANDS) clean

all: $(BINARIES)

$(BINARIES):bin/%: 
	$(GO_INSTALL) $*

twopc-coord: bin/twopc
	$(BIN_DIR)/twopc ":7071" ":7072"

twopc-db1: bin/twopc
	$(BIN_DIR)/twopc -coord=false -id=1 -addr=":7071" ":7070"

twopc-db2: bin/twopc
	$(BIN_DIR)/twopc -coord=false -id=2 -addr=":7072" ":7070"

twopc-icet: bin/icet
	$(BIN_DIR)/icet $(THIS_DIR)/src/twopc/twopc.go

clean:
	$(GO) clean -i $(patsubst bin/%,%,$(BINARIES))
