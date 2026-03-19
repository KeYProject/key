//https://mikemybytes.com/2022/02/16/java-records-and-compact-constructors/
record // package-private
Name(// package-private
String name) {

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

    Point(int x, int y) {
        // boring!
        this.x = x;
        this.y = y;
    }

    Point(int x) {
        // a bit weird...
        // ... but perfectly fine for the compiler
        this(x, 0);
    }

    Point() {
        // fails with: 'constructor is not canonical, so its first
        //              statement must invoke another constructor'
    }
}
