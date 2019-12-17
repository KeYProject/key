<head>
<style type="text/css">
body, html {
    height: 100%;
    margin: 0;
    font-family: Arial;
}

.tab {
    overflow: hidden;
    border: 1px solid #ccc;
    background-color: #f1f1f1;
}

.tab button {
    background-color: inherit;
    float: left;
    border: none;
    outline: none;
    cursor: pointer;
    padding: 14px 16px;
    transition: 0.3s;
    font-size: 20px;
}

.tab button:hover {
    background-color: #ddd;
}

.tab button.active {
    background-color: #ccc
}

.tabcontent {
    display: none;
    padding: 6px 12px;
    border: 1px solid #ccc;
    border-top: none;
    height: 80%;
}

ul, #fileTree {
	list-style-type: none;
}

#fileTree {
	margin: 0;
	padding: 0;
}

.caret {
	cursor: pointer;
	user-select: none;
}

.caret::before {
	content: "\25B6";
	color: black;
	display: inline-block;
	margin-right: 6px;
}

.caret-down::before {
	transform: rotate(90deg);
}

.nested {
	display: none;
}

.active {
	display: block;
}

</style>
</head>

<body>

<div class="tab">
    <button class="tablinks" onclick="openTab(event, 'files')" id="defaultOpen">files</button>
    <button class="tablinks" onclick="openTab(event, 'contracts')">contracts</button>
</div>

<div id="files" class="tabcontent">
    <h3>File contained in proof bundle:</h3>
    <p>This tab contains the filetree</p>
	<ul id="fileTree">
		<li><span class="caret">\$bundleFileName</span>
			<ul class="nested">
				<li><span class="caret">src</span>
					<ul class="nested">
						<li>...</li>
					</ul>
				</li>
				<li><span class="caret">cp</span>
					<ul class="nested">
						<li>...</li>
					</ul>
				</li>
				<li><span class="caret">bcp</span>
					<ul class="nested">
						<li>...</li>
					</ul>
				</li>
				<li>p1.proof</li>
				<li>p2.proof</li>
				<li>problem.key</li>
				<li>projekt.kproj</li>
			</ul>
		</li>
	</ul>
</div>

<div id="contracts" class="tabcontent">
    <h3>File contained in proof bundle:</h3>
    <p>This tab contains the contracts</p>
</div>

<script type="text/javascript">
function openTab(evt, tabName) {
    var i, tabcontent, tablinks;

    tabcontent = document.getElementsByClassName("tabcontent");
    for (i = 0; i < tabcontent.length; i++) {
        tabcontent[i].style.display = "none";
    }

    tablinks = document.getElementsByClassName("tablinks");
    for (i = 0; i < tablinks.length; i++) {
        tablinks[i].className = tablinks[i].className.replace(" active", "");
    }

    document.getElementById(tabName).style.display = "block";
    evt.currentTarget.className += " active";
}

document.getElementById("defaultOpen").click()

var toggler = document.getElementsByClassName("caret");
var i;

for (i = 0; i < toggler.length; i++) {
	toggler[i].addEventListener("click", function() {
		this.parentElement.querySelector(".nested").classList.toggle("active");
		this.classList.toggle("caret-down");
	});
}
</script>
</body>
