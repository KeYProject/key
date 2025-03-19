package comment;

public class Client {
	public void access(SecureList<?> list) {
		try {
			for (int i=0; i<list.size(); i++) {
				Object o = list.get(i);
				list.remove(o);
			}
		} catch (InsufficientRightsException e) {
			e.printStackTrace();
		}
	}
}
