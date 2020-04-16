<table id="contractTable">
    <thead class="tableHead">
    <tr>
        <th rowspan="2" class="clickable" onclick="sortTable('contractTable', 0, 2)">Contract</th>
        <th rowspan="2" class="clickable" onclick="sortTable('contractTable', 1, 2)">Source File</th>
        $! <th>Proof Obligation</th> !$
        <th colspan="5" style="text-align:center;">Proof</th>
    </tr>
    <tr>
        <th>File</th>
        <th class="clickable" onclick="sortTable('contractTable', 3, 2)">Settings ID</th>
        <th>Status</th>
        <th>Replay Result</th>
        <th>Statistics</th>
    </tr>
    </thead>
    <tbody>
        $contracts:{c | $line(dataView=dataView, data=c, cd=cd)$}$
    </tbody>
</table>
