interface MyList {
       
    public void add(Object element);
    
    public /*@ pure*/ Object get(int index);       
}
