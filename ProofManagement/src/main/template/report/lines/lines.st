<table>
    <thead>
    <tr>
        <th>Contract</th>
        <th>Source File</th>
        $! <th>Proof Obligation</th> !$
        <th colspan="4" style="text-align:center;">Proof</th>
    </tr>
    <tr>
        <th></th>
        <th></th>
        <th>File</th>
        <th>Settings</th>
        <th>Status</th>
        <th>Statistics</th>
    </tr>
    </thead>
    <tbody>
        $contracts:{c | $line(data=c)$}$
    </tbody>
</table>