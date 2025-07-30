<#-- @ftlvariable name="checkerData" type="org.key_project.proofmanagement.check.CheckerData" -->
<#-- @ftlvariable name="style" type="String" -->
<#-- @ftlvariable name="scripts" type="String" -->
<#-- @ftlvariable name="title" type="String" -->
<#-- @ftlvariable name="bundleFileName" type="String" -->
<#-- @ftlvariable name="treeRoot" type="org.key_project.proofmanagement.check.PathNode" -->
<#-- @ftlvariable name="entries" type="java.util.List<org.key_project.proofmanagement.check.CheckerData.ProofEntry>" -->
<#-- @ftlvariable name="graph" type="org.key_project.proofmanagement.check.dependency.DependencyGraph" -->
<!DOCTYPE html>
<html lang="en">
<head>
	<meta charset="UTF-8">
	<title>${title}</title>
	<style>
		${style}
	</style>
</head>

<body>

<div class="nav">
	<a class="tablinks" href="#overview" id="defaultOpen">Overview</a>
	<a class="tablinks" href="#files">Files</a>
	<a class="tablinks" href="#contracts">Contracts</a>
	<a class="tablinks" href="#dependencies">Dependencies</a>
</div>

<div id="overview" class="tabcontent default">

	<div id="bundleName">
		Bundle: ${checkerData.pbh.bundleName!"n/a"}
	</div>


	<div id="checks-ran">
		Checks run:
      <#list checkerData.checks as key, c>
          ${c}<#sep>, </#sep>
      </#list>
	</div>

	<div class="report-date">Date of report: ${checkerData.checkDate}</div>

	<div class="overall-status status-${checkerData.globalState}">Overall Status: ${checkerData.globalState}</div>

	<div>
		<h3>Contracts Overview</h3>
      <#assign  total=checkerData.bundleProofCount()
      proven=checkerData.provenCount()
      lemmaLeft=checkerData.lemmaLeftCount()
      unproven=checkerData.unprovenCount()
      data=checkerData >

      <#assign provenPercent=proven/total*100
      depsLeftPercent=lemmaLeft/total*100
      unprovenPercent=unproven/total*100 >

		<svg version="1.1"
		     width="500" height="200"
		     xmlns="http://www.w3.org/2000/svg">

			<g transform="translate(0,0)">
				<g transform="scale(5,1)">
					<rect x="0" y="0" width="${provenPercent}" height="25" stroke-width="0" fill="#4CAF50"/>
					<rect x="${provenPercent}" y="0" width="${depsLeftPercent}" height="25" stroke-width="0" fill="#f48336"/>
					<rect x="${depsLeftPercent+provenPercent}" y="0" width="${unprovenPercent}" height="25" stroke-width="0"
					      fill="#f44336"/>
				</g>

				<g transform="translate(35,40)">
					<g transform="translate(0,0)">
						<rect x="0" y="0" width="10" height="10" stroke-width="0" fill="#4CAF50"/>
						<text x="15" y="10" alignment-baseline="middle">proven (${proven})</text>
					</g>
					<g transform="translate(120,0)">
						<rect x="0" y="0" width="10" height="10" stroke-width="0" fill="#f48336"/>
						<text x="15" y="10">dependencies left (${lemmaLeft})</text>
					</g>
					<g transform="translate(320,0)">
						<rect x="0" y="0" width="10" height="10" fill="#f44336"/>
						<text x="15" y="10">unproven (${unproven})</text>
					</g>
				</g>
			</g>
		</svg>

		<!--
		<div>
			<div>
				<span class="legend">proven</span>
				<span style="width: calc(${proven/total*100}%); background:#4CAF50" class="bar"></span>
					${proven} (${proven/total*100}%)
			</div>
			<div>
				<span class="legend">dependencies left</span>
				<span style="width: calc(${lemmaLeft/total*100}%); background:#f48336;" class="bar"></span>
          ${lemmaLeft} (${lemmaLeft/total*100}%)
			</div>
			<div>
				<span class="legend">unproven</span>
				<span style="width: calc(${unproven/total*100}%); background:#f44336;" class="bar"></span>
          ${unproven} (${unproven/total*100}%)
			</div>
		</div>
        -->


	</div>

	<div class="log-messages">
		<h3>Log messages</h3>
		<div style="text-align:end;">
			<div>
				<input type="checkbox" id="errors" value="4" checked>
				<label for="errors">Error</label>
				<input type="checkbox" id="warnings" value="3" checked>
				<label for="warnings">Warning</label>
				<input type="checkbox" id="info" value="2" checked>
				<label for="info">Information</label>
				<input type="checkbox" id="debug" value="0" checked>
				<label for="debug">Debug</label>
			</div>
		</div>
		<div id="messages">
        <#list checkerData.messages as msg>
            <#escape x as x>
							<div class="logline loglevel-${msg.level().ordinal()}">
                  ${msg}
							</div>
            </#escape>
        </#list>
		</div>
	</div>
</div>

<div id="files" class="tabcontent">
	<h3>Files found inside proof bundle:</h3>

    <#macro tree_folder f>
			<span class="caret">${f}</span>
			<ul class="nested active">
          <#list f.children as c>
              <@tree node=c />
          </#list>
			</ul>
    </#macro>

    <#macro tree node>
			<ul id="fileTree">
				<li>
            <#if node.children?has_content>
                <@tree_folder node />
            <#else>
                ${node}
            </#if>
				</li>
			</ul>
    </#macro>
    <@tree treeRoot />
</div>

<div id="contracts" class="tabcontent">
	<h3>Contracts with proof inside bundle:</h3>
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
    <#list entries as entry>
			<tr class="blue">
				<td>
					class: ${entry.contract.KJT.javaType.name}<br>
					target: ${entry.contract.target.name()}<br>
					type: ${entry.contract.displayName}
				</td>
				<td>
					<div title="${entry.sourceFile}"> ${entry.shortSrc} </div>
				</td>
				<td>
					<div title="${entry.proofFile.toFile()}"> ${entry.proofFile.toFile().name}</div>
				</td>
				<td><a href="#settings-${entry.settingsId()}">#${entry.settingsId()?string("00")}</a></td>
				<td>${entry.loadingState}</td>
				<td>${entry.replayState}</td>
				<td>${entry.proofState}</td>
				<td>${entry.dependencyState}</td>

          <#if checkerData.checks.replay??>
              <#if entry.replaySuccess()>
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
    </#list>
		</tbody>
	</table>

	<h3>Contracts declared inside bundle without proof:</h3>
	<table id="prooflessTable">
		<thead class="tableHead">
		<tr>
			<th class="clickable" onclick="sortTable('prooflessTable', 0, 1)">Contract</th>
		</tr>
		</thead>
		<tbody>
    <#list checkerData.contractsWithoutProof as c>
			<tr class="blue">
				<td>
					class: ${c.KJT.javaType.name}<br>
					target: ${c.target.name()}<br>
					type: ${c.displayName}
				</td>
			</tr>
    </#list>
		</tbody>
	</table>
	<h3>Settings comparison:</h3>
	<table>
		<thead class="tableHead">
		<tr>
			<th>ID</th>
        <#list checkerData.choiceNames as names>
					<th>${names}</th>
        </#list>
		</tr>
		</thead>
		<tbody>
    <#list checkerData.shortChoices2Id as choices , value>
			<tr id="settings-$entry.value$" class="blue">
				<td>${value}</td>
          <#list checkerData.choiceNames as name>
						<td>${choices[name]???string('yes','no')}</td>
          </#list>
				<!--This works:
						<#list choices as category, option >
						<td>${category} : ${option}</td>
					</#list>-->
			</tr>
    </#list>
		</tbody>
	</table>
</div>

<div id="dependencies" class="tabcontent">
	<h3>Dependencies between contracts:</h3>
    <#if graph?? >
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
        <#list graph.node2SCC as node, scc>
					<tr class="blue">
						<td style="background-color:hsl(calc(360/${graph.nodes?size} * ${scc.id}),60%,90%);">
                ${node.contract.name}
						</td>
						<td style="background-color:hsl(calc(360/${graph.nodes?size} * ${scc.id}),60%,90%);">
							#${scc.id?string("00")}
                <#if scc.legal>
									(legal)
                <#else>
									(illegal)
                </#if>
						</td>
						<td>&#10230;</td>
						<td>
                <#list node.dependencies?keys as d>
                    ${d.contract.name}<br>
                </#list>
						</td>
					</tr>
        </#list>
				</tbody>
			</table>

			<!-- make sure the table is sorted by SCC initially for a nice view -->
			<script type="text/javascript">
          sortTable('depTable', 1, 1);
			</script>
    <#else>
			Dependency check has not been enabled. Use <code>--dependency</code> flag to enable it.
    </#if>
</div>


<script type="text/javascript">
    ${scripts}
</script>

</body>
</html>
