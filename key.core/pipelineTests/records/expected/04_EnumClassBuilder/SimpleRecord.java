public record SimpleRecord(/*@ nullable */ String name) implements Serializable {

    SimpleRecord(String name) {
        this.name = name;
    }
}
