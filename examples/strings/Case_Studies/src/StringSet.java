public class StringSet {

	private /*@ spec_public nullable @*/ String[] elements;
	private /*@ spec_public @*/ int size;
	/*@ public instance invariant
		this.size > 0;
	  @*/
	/*@ public instance invariant
		this.elements != null && this.elements.length == this.size;
	  @*/
	
	public StringSet (int size) {
		assert (size > 0);
		this.size = size;
		elements = new String[size];
	}
	
	/*@ public normal_behavior
		requires s != null;
		requires this.elements[(s.hashCode() % this.size)] == null;
		assignable this.elements[(s.hashCode() % this.size)];
		ensures this.elements[(s.hashCode() % this.size)] == s;
		ensures \result == true;
		
		also
		
		public normal_behavior
		requires s != null;
		requires this.elements[(s.hashCode() % this.size)] != null;
		assignable \nothing;
		ensures \result == elements[(s.hashCode() % this.size)].equals(s);
		
		also
		
		public normal_behavior
		requires s == null;
		assignable \nothing;
		ensures \result == false;
	  @*/
	public boolean insert (String /*@ nullable @*/ s) {
		if (s == null || s.hashCode() % size >= size) {
			return false;
		} else {
			if (elements[s.hashCode() % size] == null) {
				elements[s.hashCode() % size] = s;
				return true;
			} else {
				return elements[s.hashCode() % size].equals(s);
			}
		}
	}
	
	/*@ public normal_behavior
		requires s != null;
		assignable \nothing;
		ensures \result == s.equals(this.elements[s.hashCode() % this.size]);
		
		also
		
		public normal_behavior
		requires s == null;
		assignable \nothing;
		ensures \result == false;
	  @*/
	public boolean contains (String /*@ nullable @*/ s) {
		if (s == null || s.hashCode() % size >= size) {
			return false;
		} else {
			return s.equals(elements[s.hashCode() % size]);
		}
	}
		
}
