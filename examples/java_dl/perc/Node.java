public class Node{

    public Node next;

    public Object obj;

    public @NoLocalScope @ExternallyConstructedScope Node(Object o){
	obj = o;
    }

}
