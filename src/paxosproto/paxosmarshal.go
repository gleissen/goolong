package paxosproto

import (
	"io"
)

func (p *ProposalReply) Marshal(wire io.Writer) {
	var b [9]byte
	bs := b[:9]
	tmp32 := p.Rw
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = p.Rwt
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	bs[8] = byte(p.Success)
	wire.Write(bs)
}

func (p *ProposalReply) Unmarshal(wire io.Reader) error {
	var b [9]byte
	bs := b[:9]
	_, err := io.ReadAtLeast(wire, bs, 9)
	p.Rw = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.Rwt = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.Success = uint8(bs[8])
	return err
}
