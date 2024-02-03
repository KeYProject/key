/**
 * This package containes generated list and iterator types.
 * <DL>
 * <DT>Implementation</DT>
 * <DD>
 * The elements are addressed by indices rather than iterators or
 * explicite nodes. This saves storage and provides a slim interface.
 * <p>
 * The default implementations end with "ArrayList" and use the common
 * array doubling technique.
 * If elements must be added and the number is known a-priori (e.g. before
 * concatenating a set of lists), it is wise to increase the capacity of the
 * array with {@link recoder.list.ObjectArrayList#ensureCapacity}.
 * </DD>
 * <DT>Genericity</DT>
 * <DD>
 * The lists are heterogeneous emulations of generic classes.
 * Specialized versions inherit from {@link recoder.list.ObjectList} and delegate
 * to the "untyped" (i.e. Object type) methods. Since the untyped
 * methods are not public in {@link recoder.list.ObjectList}, this is quite safe.
 * </DD>
 * <DT>Mutability</DT>
 * <DD>
 * The standard list interfaces are read-only. To modify a list, one must
 * use a XYZMutableList that extends the corresponding XYZList interface.
 * <p>
 * The read-only List interfaces are additionally inherited in parallel to
 * the relations between the element types: A {@link recoder.list.ModifierList}
 * extends a {@link recoder.list.ProgramElementList} which in turn extends an
 * {@link recoder.list.ModelElementList} which extends the
 * {@link recoder.list.ObjectList}. With this technique, it is possible
 * to add a {@link recoder.list.ModifierList} to a
 * {@link recoder.list.ProgramElementMutableList}
 * (the {@link recoder.list.ObjectArrayList#add} method expects a
 * {@link recoder.list.ProgramElementList} which is a proper superclass of
 * {@link recoder.list.ModifierList}).
 * Note that to avoid covariance problems (i.e. the preconditions of e.g.
 * add methods are not in a sense compatible in polymorphic contexts), the
 * mutable lists are <em>not</em> inherited from each other.
 * </DD>
 * </DL>
 */
package recoder.list;
