#!/bin/bash

func() {
    echo "digraph G{" > out.dot
    
    for i in *graph.dot
    do
        if test -f "$i"
        then
            dot -Tpng $i > $i.png
            echo '"_'${i%graph.dot}'"[image="'$i'.png", label=""];' >> out.dot
        fi
    done
    echo "}" >> out.dot
    dot -Tpng out.dot > out.png
}

func
