#!/bin/bash
export CORE="RGref/DSL/LinearEnv.v RGref/DSL/DSL.v RGref/DSL/Theories.v RGref/DSL/Core.v RGref/DSL/Monad.v"
export EXAMPLES="PosMonotonicCounter.v AppendOnlyLinkedList.v MonotonicCounter.v PrependOnlyPureList.v CounterModule.v RCC.v ReferenceImmutability.v LinkedList.v MemoTable.v"
export BUGS="KnownUnsoundnessExamples.v"
coq_makefile -arg -impredicative-set -R RGref RGref $CORE $EXAMPLES $BUGS > Makefile
touch .depend
make depend
make
