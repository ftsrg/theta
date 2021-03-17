#!/bin/bash

func() {
    echo "digraph G{" > out.dot
    for i in */
    do
        if [ -d "$i" ]
        then
            (cd $i && func)
            cp $i/out.png ${i%/}.png
            echo '"_'${i%/}'_"[image="'${i%/}'.png", label=""];' >> out.dot
        fi
    done
    
    last="start"
    
    for i in *graph.dot
    do
        if test -f "$i"
        then
            dot -Tpng $i > $i.png
            echo '"_'${i%graph.dot}'"[image="'$i'.png", label=""];' >> out.dot
            if [[ -d "${i%graph.dot}" ]]
            then
                echo '"_'${i%graph.dot}'" -> "_'${i%graph.dot}'_";' >> out.dot
            fi
            echo $last ' -> "_'${i%graph.dot}'";' >> out.dot
            last="_${i%graph.dot}"
        fi
    done
    echo "}" >> out.dot
    dot -Tpng out.dot > out.png
}

func
