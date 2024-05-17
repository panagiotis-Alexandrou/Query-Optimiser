package sjdb;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

public class Estimator implements PlanVisitor {

	private int totalCost = 0;

	public Estimator() {
		// empty constructor
	}

	/* 
	 * Create output relation on Scan operator
	 *
	 * Example implementation of visit method for Scan operators.
	 */
	public void visit(Scan op) {
		Relation input = op.getRelation();
		Relation output = new Relation(input.getTupleCount());
		
		Iterator<Attribute> iter = input.getAttributes().iterator();
		while (iter.hasNext()) {
			output.addAttribute(new Attribute(iter.next()));
		}
		
		op.setOutput(output);
		addToTotalCost(output.getTupleCount());
	}

	public void visit(Project op) {
		// get the child operator
		Operator child = op.getInput();
		// get the input Relation
		Relation inputRelation = child.getOutput();
		int tuples = inputRelation.getTupleCount();
		// T(π(R)) = T(R)
		Relation output = new Relation(tuples);

		for (Attribute projectAtr : op.getAttributes()) {
			for(Attribute relationAtr: inputRelation.getAttributes()){
				if (projectAtr.equals(relationAtr)){
					output.addAttribute(relationAtr);
				}
			}
		}
		op.setOutput(output);
		addToTotalCost(output.getTupleCount());
	}
	
	public void visit(Select op) {
		// two cases 1) atr = val 2) atr1 = atr2
		Operator child = op.getInput();
		Relation inputRelation = child.getOutput();
		// T(R)
		int tuples = inputRelation.getTupleCount();
		Relation output;
		int cost ;


		Predicate predicate = op.getPredicate();
		Attribute predLeft = predicate.getLeftAttribute();
		Attribute predRight = predicate.getRightAttribute();

		// if case (1)
		if(predicate.equalsValue()){
			Attribute inputLeft = inputRelation.getAttribute(predLeft);
			// V(R/A)
			int values = inputLeft.getValueCount();

			// T(σ(R)) = T(R)/V(R,A)
			float div = (float) tuples/ values;

			cost = Math.round(div);

			output = new Relation(cost);

			for (Attribute attribute: inputRelation.getAttributes()){
				if (attribute.equals(inputLeft)){
					// V(σA=val(R),A) = 1
					output.addAttribute(new Attribute(attribute.getName(),1));
				}

				else{
				output.addAttribute(new Attribute(attribute));
				}
			}

		}

		else{

			Attribute inputLeft = inputRelation.getAttribute(predLeft);

			Attribute inputRight = inputRelation.getAttribute(predRight);

			int max = Math.max(inputLeft.getValueCount(),inputRight.getValueCount());

			int min =  Math.min(inputLeft.getValueCount(),inputRight.getValueCount());

			float div = tuples/max;
			cost = Math.round(div);

			output = new Relation(cost);

			for (Attribute attribute : inputRelation.getAttributes()){

				if(attribute.equals(inputLeft) || attribute.equals(inputRight)){
					output.addAttribute(new Attribute(attribute.getName(),min));
				}
				else{
					output.addAttribute(new Attribute(attribute));
				}
			}

		}

		op.setOutput(output);
		addToTotalCost(output.getTupleCount());
	}
	
	public void visit(Product op) {

		Operator childLeft = op.getLeft();
		Operator childRight = op.getRight();

		Relation leftInputRelation = childLeft.getOutput();
		Relation rightInputRelation = childRight.getOutput();

		int tuplesLeft = leftInputRelation.getTupleCount();
		int tuplesRight = rightInputRelation.getTupleCount();

		// T(RxS) = T(R) * T(S)
		int cost = tuplesLeft * tuplesRight;

		Relation output = new Relation(cost);

		for (Attribute attributeLeft : leftInputRelation.getAttributes()){

			output.addAttribute(new Attribute(attributeLeft));

		}
		for (Attribute attributeRight : rightInputRelation.getAttributes()){

			output.addAttribute(new Attribute(attributeRight));

		}

		op.setOutput(output);
		addToTotalCost(output.getTupleCount());
	}
	
	public void visit(Join op) {

		Predicate predicate = op.getPredicate();
		Attribute joinAttributeLeft = op.getPredicate().getLeftAttribute();
		Attribute joinAttributeRight = op.getPredicate().getRightAttribute();

		Operator childLeft = op.getLeft();
		Operator childRight = op.getRight();

		Relation leftInputRelation = childLeft.getOutput();
		Relation rightInputRelation = childRight.getOutput();

		int tuplesLeft = leftInputRelation.getTupleCount();
		int tuplesRight = rightInputRelation.getTupleCount();



		int leftValue = leftInputRelation.getAttribute(predicate.getLeftAttribute()).getValueCount();
		int rightValue = rightInputRelation.getAttribute(predicate.getRightAttribute()).getValueCount();

		int cost;

		int max = Math.max(leftValue,rightValue);

		// T(R Join(A=B) S) = T(R) * T(S) / max(V(R,A),V(S,B))
		float div = (tuplesLeft * tuplesRight) / max;

		cost = Math.round(div);

		Relation output = new Relation(cost);

		int min = Math.max(leftValue,rightValue);

		for(Attribute attribute : leftInputRelation.getAttributes()){
			if(attribute.equals(joinAttributeLeft)){
				output.addAttribute(new Attribute(attribute.getName(),min));
			}
			else {
				output.addAttribute(new Attribute (attribute));
			}
		}
		for(Attribute attribute : rightInputRelation.getAttributes()){
			if(attribute.equals(joinAttributeRight)){
				output.addAttribute(new Attribute(attribute.getName(),min));
			}
			else {
				output.addAttribute(new Attribute (attribute));
			}
		}

		op.setOutput(output);
		addToTotalCost(output.getTupleCount());

	}

	public int getTotalCost(){
		return totalCost;
	}
	public void addToTotalCost(int cost){
		totalCost += cost;
	}
	 public  int estimateCost(Operator plan){
		totalCost = 0;
		plan.accept(this);
		return totalCost;
	 }
}
