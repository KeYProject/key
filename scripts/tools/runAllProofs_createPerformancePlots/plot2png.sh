#!/usr/bin/gnuplot

set term pngcairo # antialiasing: http://stackoverflow.com/questions/9080832/output-png-from-gnuplot-is-not-as-good-as-the-figure-from-prompt-shell

set title "computeCost() statistics" # the title printed above the graph
set key below # print curve titles below graph
set grid # adds dotted grid lines to the output graph

set xlabel "number of ast nodes"

set ylabel "computeCost average time per invocation"
set output ruledatalocation."_AST_AVGTIME.png"
plot ruledatalocation.".data" using 2:6 with points pointtype 7 pointsize .5 notitle
set ylabel "computeCost total time"
set output ruledatalocation."_AST_TOTALTIME.png"
plot ruledatalocation.".data" using 2:5 with points pointtype 7 pointsize .5 notitle
set ylabel "computeCost total invocations"
set output ruledatalocation."_AST_TOTALINVOCATIONS.png"
plot ruledatalocation.".data" using 2:4 with points pointtype 7 pointsize .5 notitle

set xlabel "proof tree depth"

set ylabel "computeCost average time per invocation"
set output ruledatalocation."_PROOFTREEDEPTH_AVGTIME.png"
plot ruledatalocation.".data" using 3:6 with points pointtype 7 pointsize .5 notitle
set ylabel "computeCost total time"
set output ruledatalocation."_PROOFTREEDEPTH_TOTALTIME.png"
plot ruledatalocation.".data" using 3:5 with points pointtype 7 pointsize .5 notitle
set ylabel "computeCost total invocations"
set output ruledatalocation."_PROOFTREEDEPTH_TOTALINVOCATIONS.png"
plot ruledatalocation.".data" using 3:4 with points pointtype 7 pointsize .5 notitle

