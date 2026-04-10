<tr class="blue">
    <td style="background-color:hsl(calc(360/$graph.nodes.size$ * $graph.node2SCC.(node).id$),60%,90%);">$node.contract.name; format="xml-encode"$</td>
    <td style="background-color:hsl(calc(360/$graph.nodes.size$ * $graph.node2SCC.(node).id$),60%,90%);">$\\$
        #$graph.node2SCC.(node).id; format="%02d"$$\\$
        $if(graph.node2SCC.(node).legal)$ (legal)$\\$
        $else$ (illegal)$\\$
        $endif$$\\$
    </td>
    <td>&#10230;</td>
    <td>$node.dependencies.keys:{d | $d.contract.name; format="xml-encode"$<br>}$</td>
</tr>