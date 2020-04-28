<head>
    <meta charset="UTF-8">
    <style type="text/css">
        $style()$
    </style>
</head>

<body>

<div class="tab">
    <button class="tablinks" onclick="openTab(event, 'overview')" id="defaultOpen">Overview</button>
    <button class="tablinks" onclick="openTab(event, 'files')">Files</button>
	<button class="tablinks" onclick="openTab(event, 'contracts')">Contracts</button>
	<button class="tablinks" onclick="openTab(event, 'dependencies')">Dependencies</button>
</div>

<div id="overview" class="tabcontent">
$/overview/overview(cd=checkerData)$
</div>

<div id="files" class="tabcontent">
    <h3>Files found inside proof bundle:</h3>
	$/tree/tree(node=treeRoot)$
</div>

<div id="contracts" class="tabcontent">
    <h3>Contracts with proof inside bundle:</h3>
    $/lines/lines(cd=checkerData, entries=entries)$
    <h3>Contracts declared inside bundle without proof:</h3>
    $/lines/prooflessContracts(cd=checkerData)$
    <h3>Settings comparison:</h3>
    $/settings/settings(cd=checkerData)$
</div>

<div id="dependencies" class="tabcontent">
    <h3>Dependencies between contracts:</h3>
    $if(graph)$
        $/dependency/dependencies(graph=graph)$
    $else$
        Dependency check has not been enabled. Use <code>--dependency</code> flag to enable it.
    $endif$
</div>

$script()$

</body>
