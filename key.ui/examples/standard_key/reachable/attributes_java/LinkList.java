public class LinkList {


    private ListElement head;


    public void reverse() {
	if (head != null) {
	    head = head.reverse();
	}	
    }

}
