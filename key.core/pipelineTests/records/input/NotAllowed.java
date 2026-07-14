//https://mikemybytes.com/2022/02/16/java-records-and-compact-constructors/


record Name(String name) { // package-private

    // fails with: 'invalid canonical constructor in record Name
    //              (attempting to assign stronger access privileges;
    //              was package)'
    private Name(String name) {
        this.name = name;
    }

    static Name of(String name) {
        return new Name(name);
    }
}


record Point(int x, int y) {
    Point(int x, int y) { // boring!
        this.x = x;
        this.y = y;
    }

    Point(int x) {  // a bit weird...
        this(x, 0); // ... but perfectly fine for the compiler
    }

    Point() {
        // fails with: 'constructor is not canonical, so its first
        //              statement must invoke another constructor'
    }
}
