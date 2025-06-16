<#-- @ftlvariable name="checkerData" type="org.key_project.proofmanagement.check.CheckerData" -->
<#-- @ftlvariable name="style" type="String" -->
<#-- @ftlvariable name="scripts" type="String" -->
<#-- @ftlvariable name="title" type="String" -->
<#-- @ftlvariable name="bundleFileName" type="String" -->
<#-- @ftlvariable name="treeRoot" type="org.key_project.proofmanagement.check.PathNode" -->
<#-- @ftlvariable name="entries" type="java.util.List<org.key_project.proofmanagement.check.CheckerData.ProofEntry>" -->
<#-- @ftlvariable name="graph" type="org.key_project.proofmanagement.check.dependency.DependencyGraph" -->

<html lang="en">
<head>
	<meta charset="UTF-8">
	<title>$title$</title>
	<style>
		${style}
	</style>
	<script type="javascript">
      ${scripts}
	</script>
</head>

<body>

<div class="tab">
	<button class="tablinks" onclick="openTab(event, 'overview')" id="defaultOpen">Overview</button>
	<button class="tablinks" onclick="openTab(event, 'files')">Files</button>
	<button class="tablinks" onclick="openTab(event, 'contracts')">Contracts</button>
	<button class="tablinks" onclick="openTab(event, 'dependencies')">Dependencies</button>
</div>

<div id="overview" class="tabcontent">
    <#include "overview/overview.ftl" >
</div>

<div id="files" class="tabcontent">
	<h3>Files found inside proof bundle:</h3>
    <#include "tree/tree.ftl" > // (node=treeRoot)$
</div>

<div id="contracts" class="tabcontent">
	<h3>Contracts with proof inside bundle:</h3>
    <#include "lines/lines.ftl" >
	//(cd=checkerData, entries=entries)$
	<h3>Contracts declared inside bundle without proof:</h3>
    <#include "lines/prooflessContracts.ftl" >
	(cd=checkerData)$
	<h3>Settings comparison:</h3>
    <#include "settings/settings.ftl">(cd=checkerData)$
</div>

<div id="dependencies" class="tabcontent">
	<h3>Dependencies between contracts:</h3>
    <#if graph >
        <#include "dependency/dependencies.ftl">
    <#else>
			Dependency check has not been enabled. Use <code>--dependency</code> flag to enable it.
    </#if>
</div>

<script type="text/javascript">
    // make the filetree foldable/expandable
    let toggler = document.getElementsByClassName("caret");
    for (let i = 0; i < toggler.length; i++) {
        toggler[i].addEventListener("click", function () {
            this.parentElement.querySelector(".nested").classList.toggle("active");
            this.classList.toggle("caret-down");
        });
    }

    // ensure that the overview tab is opened when the file is loaded
    document.getElementById("defaultOpen").click()
</script>
</body>
</html>