#!/bin/zsh

helper() {
	printf '%-20s ' ${1:t}
		sed -e '/^[[:space:]]*\/\//d' $1 | \
		sed -r ':a; s%(.*)/\*.*\*/%\1%; ta; /\/\*/ !b; N; ba' | \
		sed '/^[[:space:]]*$/d' |\
		wc -l
}

{ 
	for f in $(find . -maxdepth 3 -name '*.go'); do
		helper $f
	done
} | sort
