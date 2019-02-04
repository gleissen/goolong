#!/bin/zsh

THIS_DIR=${0:A:h}

build_brisk() {
	make -C $THIS_DIR/brisk-sequentialize
}

build_vcgen() {
	pushd $THIS_DIR/vcgen
	stack build
	popd
}

build_benchmarks() {
	make -C $THIS_DIR
}

build_brisk && build_vcgen && build_benchmarks
