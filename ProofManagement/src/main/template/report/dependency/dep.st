<tr class="blue">
    <td style="background-color:hsl(calc(360/$graph.nodes.size$ * $graph.node2SCC.(node).id$),60%,90%);">$node.contract.name$</td>
    <td style="background-color:hsl(calc(360/$graph.nodes.size$ * $graph.node2SCC.(node).id$),60%,90%);">$\\$
        #$graph.node2SCC.(node).id$$\\$
        $if(graph.node2SCC.(node).legal)$ (legal)$\\$
        $else$ (illegal)$\\$
        $endif$$\\$
    </td>
    <td>&#10230;</td>
    <td>$node.dependencies.keys:{d | $d.contract.name$<br>}$</td>
</tr>