//normal basic iterator, except for the violate() method
public class MyIterator {

    protected MyNode pos;

    public MyIterator(MyNode n) {
	pos = n;
    }

    public boolean hasNext() {
	return pos != null;
    }

    public Object next() {
	Object posData = pos.data;
	pos = pos.next;
	return posData;
    }

    public Object violate() {
	//this does not do anything bad, but MySubIterator overrides it with 
	//an implementation that does
        return (hasNext() ? next() : null);
    }
}
