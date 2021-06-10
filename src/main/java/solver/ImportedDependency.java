package solver;

import com.microsoft.z3.*;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public class ImportedDependency implements Dependency {
    private final String[] constants;
    private final String solverFormula;

    public ImportedDependency(String dependency) {
        String[] parts = dependency.split("\\|", 2);
        parts[0] = parts[0].trim();
        this.constants = parts[0].length() == 0 ? new String[0] : parts[0].split(",");
        this.solverFormula = parts[1];
    }

    @Override
    public BoolExpr apply(Instance instance) {
        Context context = instance.getContext();
        List<Symbol> funcSymbols = new ArrayList<>();
        List<FuncDecl> funcDecls = new ArrayList<>();
        for (String constant : constants) {
            funcSymbols.add(context.mkSymbol("!" + constant));
            funcDecls.add(context.mkFuncDecl("!" + constant, new Sort[0], context.getIntSort()));
        }
        for (Map.Entry<String, Relation> e : instance.entrySet()) {
            FuncDecl funcDecl = e.getValue().getFunction();
            funcSymbols.add(context.mkSymbol("!" + e.getKey()));
            funcDecls.add(funcDecl);
        }
        return context.mkAnd(context.parseSMTLIB2String(
                solverFormula,
                null,
                null,
                funcSymbols.toArray(new Symbol[0]),
                funcDecls.toArray(new FuncDecl[0])
        ));
    }
}
