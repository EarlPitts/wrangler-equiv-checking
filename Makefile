TARGET_DIR=ebin

REBAR3=/usr/bin/env rebar3

default: compile

all: compile test

compile:
	$(RM) ${TARGET_DIR}
	$(REBAR3) escriptize
	ln -s _build/default/bin/ ${TARGET_DIR}

clean:
	$(REBAR3) clean

test: FORCE
	$(REBAR3) eunit

FORCE:
