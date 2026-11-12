public record SimpleRecord([[JML modifiers]] String name) implements Serializable {

    SimpleRecord(String name) {
        this.name = name;
    }
}
