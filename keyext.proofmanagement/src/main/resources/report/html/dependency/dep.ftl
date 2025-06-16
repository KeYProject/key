<tr class="blue">
    <td style="background-color:hsl(calc(360/${graph.nodes?size} * ${graph.node2SCC[node].id}),60%,90%);">
        ${node.contract.name?xml}
    </td>
    <td style="background-color:hsl(calc(360/${graph.nodes?size} * ${graph.node2SCC[node].id}),60%,90%);">
        #${graph.node2SCC[node].id?string("00")}
        <#if graph.node2SCC[node].legal>
            (legal)
        <#else>
            (illegal)
        </#if>
    </td>
    <td>&#10230;</td>
    <td>
        <#list node.dependencies?keys as d>
            ${d.contract.name?xml}<br>
        </#list>
    </td>
</tr>
