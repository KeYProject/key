<table id="depTable">
    <thead class="tableHead">
    <tr>
        <th class="clickable" onclick="sortTable('depTable', 0, 1)">Proof</th>
        <th class="clickable" onclick="sortTable('depTable', 1, 1)">SCC</th>
        <th></th>
        <th>Dependencies</th>
    </tr>
    </thead>
    <tbody>
        $graph.nodes:{node | $dep(graph=graph, node=node)$}$
    </tbody>
</table>
