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
                    shouldSwitch = true;
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
            switchcount++;
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

// ensure that the overview tab is opened when the file is loaded
document.getElementById("defaultOpen").click()

//region Toggle the visibility of log-lines using checkboxes
let chkError = document.getElementById("errors");
let chkWarning = document.getElementById("warnings");
let chkDebug = document.getElementById("debug");
let chkInformation = document.getElementById("info");

const LOGLINE_CHECKBOXES = [chkError, chkWarning, chkInformation, chkDebug];

function updateLoglineVisibility() {
    document.getElementById("messages");
    for (const chk of LOGLINE_CHECKBOXES) {
        let value = chk.checked ? "block" : "none";

        let className = "loglevel-" + chk.value;
        let lines = document.getElementsByClassName(className);
        for (let it of lines) {
            it.style.display = value;
        }
    }
}
//endregion

document.addEventListener("DOMContentLoaded", () => {
    for (let it of LOGLINE_CHECKBOXES) {
        it.addEventListener("change", updateLoglineVisibility);
    }
    updateLoglineVisibility();
});


// region make FileTree toggle by keyboard
document.addEventListener("DOMContentLoaded", () => {
    for (let toggler of document.getElementsByClassName("caret")) {
        toggler.addEventListener("click", () => {
            this.parentElement.querySelector(".nested").classList.toggle("active");
            this.classList.toggle("caret-down");
        });
    }
});
//endregion