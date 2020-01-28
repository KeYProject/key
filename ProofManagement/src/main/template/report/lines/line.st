<tr>
    <td>$contract(data=data)$</td>
    <td><div title="$data.sourceFile$"> $data.shortSrc$ </div></td>
    <td><div title="$data.proofFile$"> $data.proofFile.fileName$ </div></td>
    <td>$data.proof.settings.choiceSettings.defaultChoices:{c | $data.proof.settings.choiceSettings.defaultChoices.(c)$<br>}$</td>
    $!<td>$data.proof.mgt.status$</td>!$        $! TODO: why is this always OPEN? --> looks like replay is needed to build the data structures !$
    <td>$data.replayResult.status$</td>
    <td>Nodes: $data.proof.statistics$ $!data.proof.statistics.nodes!$ <br> $! TODO: why is this always 1? --> looks like replay is needed to build the data structures !$
        $!Interactive Steps: $data.proof.statistics.interactiveSteps$ <br>
        Automode Time: $data.proof.statistics.autoModeTimeInMillis$ ms <br> !$
    </td>
</tr>