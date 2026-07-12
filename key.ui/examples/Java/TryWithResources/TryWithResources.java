public final class TryWithResources {
    /*@ ensures true; requires true; */
    public void m() throws Exception {
        // Simple try-with-resources
        try (Resource r = new Resource()) {
            r.use();
        }
        
        // Multiple resources
        try (Resource r1 = new Resource(); Resource r2 = new Resource()) {
            r1.use();
            r2.use();
        }
        
        // Java 9+ style with existing variable
        Resource existing = new Resource();
        try (existing) {
            existing.use();
        }
    }
    
    static class Resource implements AutoCloseable {
        /*@ ensures true; requires true; */
        public void use() {
            // use the resource
        }
        
        /*@ ensures true; requires true; */
        @Override
        public void close() throws Exception {
            // close the resource
        }
    }
}