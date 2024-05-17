package sjdb;

import org.w3c.dom.Attr;

import java.util.ArrayList;
import java.util.List;

public class Optimiser implements PlanVisitor{

    //plan
    // Parse Query
    // Collect all relations, selections, projections, products and joins
    // Push σ down the tree
    // Combine selections and products to make joins
    // Re-order Joins
    // Push π operators down the tree

    Estimator est ;
    ArrayList<Predicate> valuePredicates;
    ArrayList<Predicate> dualPredicates;
    ArrayList<Scan> relations;
    ArrayList<Attribute> attributes;
    ArrayList<Attribute> projects;
    Catalogue cat;


    public Optimiser(Catalogue cat){
        this.cat = cat;
        est = new Estimator();
        relations = new ArrayList<>();
        attributes = new ArrayList<>();
        valuePredicates = new ArrayList<>();
        dualPredicates = new ArrayList<>();
        projects = new ArrayList<>();



    }

    public Operator optimise(Operator plan){
        // Parse Query
        plan.accept(this);

        ArrayList<Operator> rels = pushSelects();

        ArrayList<Operator> relsInter = pushProjects(rels);

        List<Operator> subTrees = relsInter;

        while(relsInter.size() > 1){
            boolean tag = false;
            for (int i = 0 ; i<relsInter.size(); i++){

                Operator rel = relsInter.get(i);

                if(rel.getOutput()==null){
                    rel.accept(est);
                }

                for (int k = 0 ; k<dualPredicates.size() ; k++){

                    Predicate predicate = dualPredicates.get(k);

                    Attribute left = predicate.getLeftAttribute();
                    Attribute right = predicate.getRightAttribute();

                    if(rel.getOutput().getAttributes().contains(left)){

                        for (int j = 0; j<relsInter.size() ; j++){

                            Operator rel2 = relsInter.get(j);

                            if(rel2.getOutput() == null){
                                rel2.accept(est);
                            }

                            if(rel2.getOutput().getAttributes().contains(right) && i!=j ){ // self joins are not permitted

                                Operator join = new Join(rel,rel2,predicate);

                                dualPredicates.remove(predicate);

                                attributes.remove(left);
                                attributes.remove(right);

                                relsInter.remove(rel);
                                relsInter.remove(rel2);
                                relsInter.add(join);

                                if (projects.size()>0){
                                    List<Attribute> projectionAtts = new ArrayList<>();
                                    if(join.getOutput() == null){
                                        join.accept(est);
                                    }

                                    for (Attribute attribute :attributes){
                                        if(join.getOutput().getAttributes().contains(attribute))
                                            projectionAtts.add(attribute);
                                    }
                                    if(projectionAtts.size()< join.getOutput().getAttributes().size()){
                                        Operator projectedJoin = new Project(join,projectionAtts);
                                        relsInter.add(projectedJoin);
                                        relsInter.remove(join);
                                    }
                                }
                                tag = true;
                                i = relsInter.size();
                                j = relsInter.size();
                                k = dualPredicates.size();
                            }


                        }

                    }
                }

            }
            if(!tag && relsInter.size()>1){ // if join has not been found, do a cross product

                Operator rel1 = relsInter.get(0);
                Operator rel2 = relsInter.get(1);

                Operator product = new Product(rel1,rel2);
                if (projects.size()>0){
                    List<Attribute> projectionAtts = new ArrayList<>();
                    if(product.getOutput() == null){
                        product.accept(est);
                    }

                    for (Attribute attribute :attributes){
                        if(product.getOutput().getAttributes().contains(attribute))
                            projectionAtts.add(attribute);
                    }
                    if(projectionAtts.size()< product.getOutput().getAttributes().size()){
                        Operator projectedProd = new Project(product,projectionAtts);
                        relsInter.add(projectedProd);
                    }
                    else {
                        relsInter.add(product);
                    }
                }
                else {
                    relsInter.add(product);
                }

                relsInter.remove(rel1);
                relsInter.remove(rel2);

            }

        }

        Operator opt = relsInter.get(0);

        return opt;

        // Need to decide how to order Joins
        // One approach -> Join on first instance and delete the joint relations from the list


    }

    private ArrayList<Operator> pushProjects(ArrayList<Operator> rels) {

        ArrayList<Operator> afterPro = new ArrayList<>();

        for (Operator relation : rels){



            List<Attribute> attributes = new ArrayList<>();

            if(relation.getOutput() == null) {
                relation.accept(est);
            }

            for(Attribute attribute : relation.getOutput().getAttributes()){

                if(this.attributes.contains(attribute) ){
                    attributes.add(attribute);
                }

            }

            if(projects.size()<1){
                afterPro.add(relation);
            }
            else {

                afterPro.add(new Project(relation,attributes));


            }

        }
        return afterPro;
    }

    public ArrayList<Operator> pushSelects(){
        ArrayList<Operator> rels = new ArrayList<>();

        for (int i = 0 ; i<relations.size() ; i++){

            Operator relation = relations.get(i);

            for (int j = 0 ; j < valuePredicates.size() ; j++){
                Predicate pred = valuePredicates.get(j);

                if(predOnRel(pred,relation.getOutput())){
                    Operator selected = new Select(relation,pred);
                    rels.add(selected);


                    valuePredicates.remove(pred);
                    attributes.remove(pred.getLeftAttribute());
                }
            }
            // if this relation has not been added with a selection, add as it is
            if (rels.size()< i+1){

                rels.add(relation);

            }
        }

        return rels;
    }

    public boolean predOnRel(Predicate pred, Relation rel){

        Attribute left = pred.getLeftAttribute();

        if (rel.getAttributes().contains(left)){
            return true;
        }
        return false;

    }
    @Override
    public void visit(Scan op) {
        Relation rel = op.getRelation();
        relations.add(new Scan((NamedRelation) rel));
    }

    @Override
    public void visit(Project op) {
        List<Attribute> projectedAtts = op.getAttributes();
        for (Attribute attribute : projectedAtts){
            attributes.add(attribute);
            projects.add(attribute);
        }

    }

    @Override
    public void visit(Select op) {
        Predicate predicate = op.getPredicate();

        if (predicate.equalsValue()){
            valuePredicates.add(predicate);
            attributes.add(predicate.getLeftAttribute());
        }
        else {
            dualPredicates.add(predicate);
            attributes.add(predicate.getLeftAttribute());
            attributes.add(predicate.getRightAttribute());
        }


    }

    @Override
    public void visit(Product op) {
        // do nothing products are inefficient
    }

    @Override
    public void visit(Join op) {
        Predicate predicate = op.getPredicate();

        Attribute left = predicate.getLeftAttribute();
        attributes.add(left);

        Attribute right = predicate.getRightAttribute();
        attributes.add(right);
        dualPredicates.add(predicate);





    }
}
