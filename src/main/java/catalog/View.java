package catalog;

/**
 * POJO for `partitions` table in db
 */
public class View {
    long id;
    String name;
    String description;
    String query;
    long cost;
    String schema;
    String table;
    long destinationId;
    String destination;
    long dsSetId;

    public View(long id,
                String name,
                String description,
                String query,
                long cost,
                String table,
                String schema,
                long destinationId,
                String destination,
                long dsSetId) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.query = query;
        this.cost = cost;
        this.schema = schema;
        this.table = table;
        this.destinationId = destinationId;
        this.destination = destination;
        this.dsSetId = dsSetId;
    }

    public long getId() {
        return id;
    }

    public void setId(long id) {
        this.id = id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public String getQuery() {
        return query;
    }

    public void setQuery(String query) {
        this.query = query;
    }

    public long getCost() {
        return cost;
    }

    public void setCost(long cost) {
        this.cost = cost;
    }

    public String getSchema() {
        return schema;
    }

    public void setSchema(String schema) {
        this.schema = schema;
    }

    public String getTable() {
        return table;
    }

    public void setTable(String table) {
        this.table = table;
    }

    public long getDestinationId() {
        return destinationId;
    }

    public void setDestinationId(long destinationId) {
        this.destinationId = destinationId;
    }

    public String getDestination() {
        return destination;
    }

    public void setDestination(String destination) {
        this.destination = destination;
    }

    public long getDsSetId() {
        return dsSetId;
    }

    public void setDsSetId(long dsSetId) {
        this.dsSetId = dsSetId;
    }

    public String[] values() {
        return new String[]{String.valueOf(this.id),
                this.name,
                this.description,
                String.valueOf(this.cost),
                this.query,
                String.valueOf(this.destinationId),
                this.schema,
                this.table,
                String.valueOf(this.dsSetId)};
    }

}
