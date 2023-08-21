<table id="prooflessTable">
    <thead class="tableHead">
    <tr>
        <th class="clickable" onclick="sortTable('prooflessTable', 0, 1)">Contract</th>
    </tr>
    </thead>
    <tbody>
        $cd.contractsWithoutProof:{c | <tr class="blue">
            <td>$contract(contract=c)$</td>
        </tr>}$
    </tbody>
</table>