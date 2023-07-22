<table id="contractTable">
    <thead class="tableHead">
    <tr>
        <th rowspan="3" class="clickable" onclick="sortTable('contractTable', 0, 3)">Contract</th>
        <th rowspan="3" class="clickable" onclick="sortTable('contractTable', 1, 3)">Source File</th>
        <th colspan="7" style="text-align:center;">Proof</th>
    </tr>
    <tr>
        <th rowspan="2">File</th>
        <th rowspan="2" class="clickable" onclick="sortTable('contractTable', 3, 3)">Settings ID</th>
        <th colspan="4" style="text-align:center;">Status</th>
        <th rowspan="2">Statistics</th>
    </tr>
    <tr>
        <th>loaded</th>
        <th>replayed</th>
        <th>state</th>
        <th>dependencies</th>
    </tr>
    </thead>
    <tbody>
        $entries:{e | $line(entry=e, cd=cd)$}$
    </tbody>
</table>
