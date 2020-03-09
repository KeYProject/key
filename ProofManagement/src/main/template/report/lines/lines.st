<table>
    <thead class="tableHead">
    <tr>
        <th rowspan="2">Contract</th>
        <th rowspan="2">Source File</th>
        $! <th>Proof Obligation</th> !$
        <th colspan="5" style="text-align:center;">Proof</th>
    </tr>
    <tr>
        <th>File</th>
        <th>Settings</th>
        <th>Status</th>
        <th>Replay Result</th>
        <th>Statistics</th>
    </tr>
    </thead>
    <tbody>
        $contracts:{c | $line(dataView=dataView, data=c)$}$
    </tbody>
</table>