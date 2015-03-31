public abstract class ImmutableLeftistHeap<T extends Comparable<T>> implements ImmutableHeap<T> {

	@SuppressWarnings("unchecked")
	public static <T extends Comparable<T>> ImmutableLeftistHeap<T> nilHeap() {
		return (ImmutableLeftistHeap<T>) Empty.EMPTY_HEAP;
	}

	private static class Empty<S extends Comparable<S>> extends ImmutableLeftistHeap<S> {

		@SuppressWarnings("rawtypes")
		private static final ImmutableLeftistHeap<?> EMPTY_HEAP = new Empty();

		public ImmutableHeap<S> insert(S element) {
			return null;
		}
	}
}