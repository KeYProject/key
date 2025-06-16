<tr class="blue">
    <td>
        <@contract contract=entry.contract />
    </td>
    <td><div title="${entry.sourceFile}"> ${entry.shortSrc} </div></td>
    <td><div title="${entry.proofFile.toFile}"> ${entry.proofFile.toFile.name}</div></td>
    <td><a href="#settings-${entry.settingsId}">#${entry.settingsId?string("00")}</a></td>
    <td>${entry.loadingState}</td>
    <td>${entry.replayState}</td>
    <td>${entry.proofState}</td>
    <td>${entry.dependencyState}</td>

    <#if cd.checks.replay>
        <#if entry.replaySuccess>
            <td>
                Nodes: ${entry.proof.statistics.nodes} <br>
                Interactive Steps: ${entry.proof.statistics.interactiveSteps} <br>
                Automode Time: ${entry.proof.statistics.autoModeTimeInMillis} ms
            </td>
        <#else>
            <td>Replay of proof failed!</td>
        </#if>
    <#else>
        <td>
            Replay of proof is needed to display meaningful information here.<br>
            Enable via <code>--replay</code> switch.
        </td>
    </#if>
</tr>
