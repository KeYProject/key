
public class Sub extends Parent {
	public int magic() {
		return 42;
	}
	
	public class SubInner extends ParentInner {
		public int innerMagic() {
			return 42;
		}
	}
}
