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

<!-- make sure the table is sorted by SCC initially for a nice view -->
<script type="text/javascript">
    sortTable('depTable', 1, 1);
</script>
