package planner;

/**
 * Represents a column in a table.
 */
public class PrivacyColumn {
    public final String name;
    public final int  type;

    public PrivacyColumn(String name, int type) {
        this.name = name.toUpperCase();
        this.type = type;
    }

    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        PrivacyColumn other = (PrivacyColumn) obj;
        return this.name.equals(other.name) && this.type == other.type;
    }

    public int hashCode() {
        return name.hashCode() + type * 31;
    }
}
