<tr class="blue">
    <td>$contract(data=data)$</td>
    <td><div title="$data.sourceFile$"> $data.shortSrc$ </div></td>
    <td><div title="$data.proofFile$"> $data.proofFile.fileName$ </div></td>
    <td>#$data.settingsId; format="%02d"$</td>
    <td>
        $if(dataView.checks.replay)$
            $data.proof.mgt.status$
        $else$
            Replay of proof is needed to see a meaningful<br>
            proof status. Enable via <code>--replay</code> switch.
        $endif$
    </td>
    <td>
        $if(dataView.checks.replay)$
            $data.replayResult$
        $else$
            Replay of proof is needed to see replay result.<br>
            Enable via <code>--replay</code> switch.
        $endif$
    </td>
    <td>$if(dataView.checks.replay)$
            Nodes: $data.proof.statistics.nodes$ <br>  $!--> replay is needed to build the data structures --> else NPE in Proof.getStatistics!$
            Interactive Steps: $data.proof.statistics.interactiveSteps$ <br>
            Automode Time: $data.proof.statistics.autoModeTimeInMillis$ ms <br>
        $else$
            Replay of proof is needed to see statistics.<br>
            Enable via <code>--replay</code> switch.
        $endif$
    </td>
</tr>
