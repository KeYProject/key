import java.util.Date;
import java.util.Iterator;

public class SimpleGenericTest<T extends Date> implements Iterable<String> {
	@Override
	public Iterator<String> iterator() {
		return null;
	}
}
