package planner;

import org.apache.calcite.adapter.enumerable.EnumerableConvention;
import org.apache.calcite.adapter.enumerable.EnumerableRel;
import org.apache.calcite.adapter.enumerable.EnumerableRelImplementor;
import org.apache.calcite.adapter.enumerable.PhysType;
import org.apache.calcite.adapter.enumerable.PhysTypeImpl;
import org.apache.calcite.linq4j.tree.Blocks;
import org.apache.calcite.linq4j.tree.Expressions;
import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptPlanner;
import org.apache.calcite.plan.RelOptTable;
import org.apache.calcite.plan.RelTraitSet;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.RelWriter;
import org.apache.calcite.rel.core.TableScan;
import org.apache.calcite.rel.type.RelDataType;

import java.util.List;

/**
 * Relational expression representing a scan of a CSV file.
 * Like any table scan, it serves as a leaf node of a query tree.
 */
public class PrivacyTableScan extends TableScan implements EnumerableRel {
    final PrivacyTable quarkTable;

    protected PrivacyTableScan(RelOptCluster cluster, RelOptTable table,
                             PrivacyTable quarkTable) {
        super(cluster, cluster.traitSetOf(EnumerableConvention.INSTANCE), table);
        this.quarkTable = quarkTable;

        assert quarkTable != null;
    }

    @Override
    public RelNode copy(RelTraitSet traitSet, List<RelNode> inputs) {
        assert inputs.isEmpty();
        return new PrivacyTableScan(getCluster(), table, quarkTable);
    }

    @Override
    public RelWriter explainTerms(RelWriter pw) {
        return super.explainTerms(pw)
                .item("fields", table.getRowType());
    }

    @Override
    public RelDataType deriveRowType() {
        return table.getRowType();
    }

    /*@Override
    public void register(RelOptPlanner planner) {
        planner.addRule(ProjectRule.INSTANCE);
    }*/

    public Result implement(EnumerableRelImplementor implementor, Prefer pref) {
        PhysType physType =
                PhysTypeImpl.of(
                        implementor.getTypeFactory(),
                        getRowType(),
                        pref.preferArray());

        return implementor.result(
                physType,
                Blocks.toBlock(
                        Expressions.call(table.getExpression(PrivacyTable.class),
                                "project",
                                Expressions.constant(PrivacyEnumerator.identityList(
                                        getRowType().getFieldCount())))));
    }

    public PrivacyTable getQuarkTable() {
        return quarkTable;
    }

    /*@Override public boolean equals(Object obj) {
        return obj == this
                || obj instanceof PrivacyTableScan
                && quarkTable.equals(((PrivacyTableScan) obj).getQuarkTable());
    }

    @Override public int hashCode() {
        return quarkTable.hashCode();
    }*/
}