#!/bin/zsh


echo "<!html>"
echo "<html>"
echo "<body>"
dir=$1
pushd -q $dir
for goal in goal-*
do
    echo "<h2>$goal</h2>"
    pushd -q $goal
    echo '<div>'
    for aut in *.dot
    do
        png=$(basename $aut .dot).png
        filepath="$dir/$goal/$png"
        >&2 echo "$filepath"
        dot -x -Tpng $aut -o $png
        echo "<figure>"
        echo "<img src=\"$filepath\">"
        echo "<figcaption>$aut</figcaption></figure>"
    done
    echo '</div>'
    popd -q
done
echo "</body></html>"
popd -q
