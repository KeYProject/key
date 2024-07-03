public class ListElement {

    public ListElement oldNext;

    private ListElement next;

    private ListElement help;


    public ListElement reverse() {
	ListElement p = null;
	ListElement c = this; 
	ListElement tmp = null;
	while(c!=null) {
	    tmp = c;
	    c = c.next;
	    tmp.next = p;
	    p = tmp;
	}
	return p;
    }


    public ListElement getLast() {
	help = this; 
	while(help.next!=null) {
	    help = help.next;
	}
	return help;
    }
}
