<script type="text/javascript">
// id: name of table
// column: index of column for sortint (starting at index 0)
// headerSize: count of static headers at the top to skip
function sortTable(id, column, headerSize) {
  var table, rows, switching, i, x, y, shouldSwitch, dir, switchcount = 0;
  table = document.getElementById(id);
  switching = true;

  // Set the sorting direction to ascending:
  dir = "asc";

  // Make a loop that will continue until no switching has been done
  while (switching) {
    //start by saying: no switching is done:
    switching = false;
    rows = table.rows;

    // Loop through all table rows (skip table headers)
    for (i = headerSize; i < (rows.length - 1); i++) {
      shouldSwitch = false;

      /*Get the two elements you want to compare,
      one from current row and one from the next:*/
      x = rows[i].getElementsByTagName("TD")[column];
      y = rows[i + 1].getElementsByTagName("TD")[column];

      /*check if the two rows should switch place,
      based on the direction, asc or desc:*/
      if (dir == "asc") {
        if (x.innerHTML.toLowerCase() > y.innerHTML.toLowerCase()) {
          //if so, mark as a switch and break the loop:
          shouldSwitch= true;
          break;
        }
      } else if (dir == "desc") {
        if (x.innerHTML.toLowerCase() < y.innerHTML.toLowerCase()) {
          //if so, mark as a switch and break the loop:
          shouldSwitch = true;
          break;
        }
      }
    }
    if (shouldSwitch) {
      /*If a switch has been marked, make the switch
      and mark that a switch has been done:*/
      rows[i].parentNode.insertBefore(rows[i + 1], rows[i]);
      switching = true;
      //Each time a switch is done, increase this count by 1:
      switchcount ++;
    } else {
      /*If no switching has been done AND the direction is "asc",
      set the direction to "desc" and run the while loop again.*/
      if (switchcount == 0 && dir == "asc") {
        dir = "desc";
        switching = true;
      }
    }
  }
}
</script>

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
</script>

<script type="text/javascript">
function handleClick(source) {
	var messages = document.getElementById("messages");
	var spans = messages.getElementsByTagName("span");
	var filter = source.value;
	console.log(filter);
	for (const s of spans) {
		var str = s.textContent;
		if (str.startsWith(filter)) {
			if (source.checked) {
				s.style.display = "block";
			} else {
				s.style.display = "none";
			}
		}
	}
}
</script>
