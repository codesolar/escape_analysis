package submit_a2;

import java.util.*;

import com.google.common.collect.Sets;
import dont_submit.EscapeQuery;
import javafx.util.Pair;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NopStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CHATransformer;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.Targets;
import soot.toolkits.graph.BriefUnitGraph;
import soot.util.Chain;
import submit_a2.A2;
class DS{
	Map<String,Set<String>> stack;
	Map<Pair<String,String>,Set<String>> heap;
	Map<String,String> emap;
	Map<Unit,String> vis;
	Map<String,Type> oType;
	DS(Map<String,Set<String>> s ,Map<Pair<String,String>,Set<String>> h,Map<String,String> e,Map<Unit,String> v,Map<String,Type> t){
		stack = s;
		heap = h;
		emap = e;
		vis = v;
		oType = t;
	}
}


public class EscapeAnalysis extends SceneTransformer{
	CallGraph cha;
//	Map<Pair<SootClass,SootMethod>,Map<Unit,String>> vis;
//	Map<String,Type> oType;
	Map<Pair<String,String>,Unit> syncMap;
	Set<Pair<SootClass,SootMethod>> needToCheck;
	Set<Pair<SootClass,SootMethod>> workList;
	Map<Pair<SootClass , SootMethod> , Set<Unit>> invokeMap;//global
	Map<Pair<SootClass , SootMethod> , DS> Inmap;
	Map<Pair<SootClass , SootMethod> , DS> Outmap;
	Map<String,Set<String>> stackG;
	Map<Pair<String,String>,Set<String>> heapG;
	Map<String,String> EMG;
	Map<String,Set<String>> finalstackG;
	Map<Pair<String,String>,Set<String>> finalheapG;
	Map<String,String> finalEMG;
	Map<Unit,Map<String,Set<String>>> unitStack;
	Map<Unit,Map<Pair<String,String>,Set<String>>> unitHeap;
	Map<Unit,Map<String,String>> unitEM;
	
	Map<Pair<String,String>,Map<Unit,Map<String,Set<String>>>> GlobalUnitStack;
	Map<Pair<String,String>,Map<Unit,Map<Pair<String,String>,Set<String>>>> GlobalUnitHeap;
	Map<Pair<String,String>,Map<Unit,Map<String,String>>> GlobalUnitEM;
	
	Map<Unit,String> visitedNewStmt;
	Map<String,Type> objType;
	Set<Unit> setOfReturns;
	int count;
	Set<SootField> giveStaticField(Pair<SootClass,SootMethod> pair){
		//System.out.println("enter giveStaticField");
		SootClass currentClass = pair.getKey();
		Chain<SootField> AllFields = currentClass.getFields();
		Set<SootField> setOfChain = new HashSet<>();
		for(SootField sf:AllFields) {
			setOfChain.add(sf);
		}
		while(currentClass.hasSuperclass()) {
			currentClass = currentClass.getSuperclass();
			//System.out.println("PARENT CLASS = " + currentClass);
			Chain<SootField> chain2 = currentClass.getFields();
			for(SootField sf:chain2) {
				setOfChain.add(sf);
			}
		}
		Set<SootField> staticSetOfField = new HashSet<>();
		for(SootField sf:setOfChain) {
			if(sf.isStatic()) {
				staticSetOfField.add(sf);
			}
		}
		
//		System.out.println("static set of field is = " + staticSetOfField);
//		System.out.println("exit giveStaticField");
		return staticSetOfField;
	}
	

	
	
	Set<String> giveReachable(Set<String> objSet,Map<Pair<String,String>,Set<String>> heapUsed){
//		System.out.println("enter giveReachable============================");
//		System.out.println(objSet);
		Set<String> reachable = new HashSet<>();
		Set<String> Process = new HashSet<>();
		Process.addAll(objSet);
		boolean bottomDetected = false;
		while(Process.size() != 0) {
			int ps = Process.size();
			for(int i = 0;i < ps;i ++) {
				String obj = Process.iterator().next();
				Process.remove(obj);
				reachable.add(obj);
				if(obj.equals("bottom")){
					bottomDetected = true;
					break;
				}
				Type type = objType.get(obj);
				SootClass currentClass = null;
				if(type instanceof RefType) {
					RefType reftype = (RefType)type;
					currentClass = reftype.getSootClass();
					Chain<SootField> chain = currentClass.getFields();
					Set<SootField> setOfChain = new HashSet<>();
					for(SootField sf:chain) {
						if(sf.getType() instanceof RefLikeType)
							setOfChain.add(sf);
					}
					//System.out.println("CURRENT CLASS = " + currentClass);
					//System.out.println("CHAIN SIZE" + setOfChain.size());
					while(currentClass.hasSuperclass()) {
						currentClass = currentClass.getSuperclass();
						//System.out.println("PARENT CLASS = " + currentClass);
						Chain<SootField> chain2 = currentClass.getFields();
						for(SootField sf:chain2) {
							if(sf.getType() instanceof RefLikeType)
								setOfChain.add(sf);
						}
					}
					
					for(SootField sf:setOfChain) {
						Pair<String,String> pair = new Pair<String,String>(obj , sf.getName());
						if(heapUsed.containsKey(pair)) {
							Set<String> newObjSet = heapUsed.get(pair);
							Process.addAll(newObjSet);
							
						}
					}
				}
			}
			
			if(bottomDetected == true) {
				break;
			}
		}
		
		if(bottomDetected == true) {
			reachable = new HashSet<>();
			reachable.add("bottom");
		}
//		System.out.println("reachable is = " + reachable);
//		System.out.println("exit giveReachable");
		return reachable;
	}

	
	void mapCreation(Pair<SootClass,SootMethod> pair) {
		//System.out.println("enter mapCreation");
		Map<String,Set<String>> stack = new HashMap<>();
		Map<Pair<String,String>,Set<String>> heap = new HashMap<>();
		Map<String,String> EM = new HashMap<>();
		EM.put("bottom", "E");
		
		Map<String,Set<String>> stack1 = new HashMap<>();
		Map<Pair<String,String>,Set<String>> heap1 = new HashMap<>();
		Map<String,String> EM1 = new HashMap<>();
		EM1.put("bottom", "E");
		
		Map<Unit,String> vis = new HashMap<>();
		Map<String,Type> oType = new HashMap<>();
		
		Set<String> formalParams = new HashSet<>();
		
		Body arg0 = pair.getValue().getActiveBody();
		
//		List<Local> listOfParams = arg0.getParameterLocals();
//		
//		for(Local l:listOfParams) {
//			System.out.println(l.toString());
//			if(l.getType() instanceof RefLikeType) {
//				formalParams.add(l.toString());
//			}
//		}
		formalParams.add("this");
		
		//the stack and heap and EM introduced are having empty stack heap and EM map
		//formalParams store the formal parameters in the method (just the formal parameters)
			
		for(String param:formalParams) {
			Set<String> set = new HashSet<>();
			Set<String> set1 = new HashSet<>();
			stack.put(param, set);
			stack1.put(param, set1);
		}
		
		DS ds = new DS(stack,heap,EM,vis,oType);
		DS ds1 = new DS(stack1,heap1,EM1,vis,oType);
		Inmap.put(pair, ds);
		Outmap.put(pair, ds1);
		//System.out.println("exit mapCreation");
	} 
	
	
	void unitMapCreation(Pair<SootClass,SootMethod> pair) {
		//System.out.println("enter unitMapCreation");
		unitStack = new HashMap<>();
		unitHeap = new HashMap<>();
		unitEM = new HashMap<>();
		
		
		stackG = Inmap.get(pair).stack;
		heapG = Inmap.get(pair).heap;
		EMG = Inmap.get(pair).emap;
		
		Body arg0 = pair.getValue().getActiveBody();
		BriefUnitGraph cfg = new BriefUnitGraph(arg0); 
		
		//System.out.println(arg0);
//		List<Local> listOfParams = arg0.getParameterLocals();
		
		
		List<Unit> headL =  cfg.getHeads();
//		Set<Unit> heads = new HashSet<>();
		PatchingChain<Unit> AllUnits = arg0.getUnits();
		for(Unit unit:AllUnits) {
			Map<String,Set<String>> tStack = new HashMap<>();
			Map<Pair<String,String>,Set<String>> tHeap = new HashMap<>();
			Map<String,String> tEM = new HashMap<>();
			Set<String> set = new HashSet<>();
			tStack.put("this",set);
			tEM.put("bottom", "E");
			unitStack.put(unit, tStack);
			unitHeap.put(unit,tHeap);
			unitEM.put(unit, tEM);
		}

		for(Unit head:headL) {
			//temporary stack heap and EM creation , it is doing deep copy of the stack heap EM of the map of this method
			Map<String,Set<String>> tStack = new HashMap<>();
			Map<Pair<String,String>,Set<String>> tHeap = new HashMap<>();
			Map<String,String> tEM = new HashMap<>();
			
			for(Map.Entry<String, Set<String>> entry:stackG.entrySet()) {
				Set<String> set = new HashSet<>();
				set.addAll(entry.getValue());
				tStack.put(entry.getKey(), set);
			}
			
			for(Map.Entry<Pair<String,String>,Set<String>> entry:heapG.entrySet()) {
				Set<String> set = new HashSet<>();
				set.addAll(entry.getValue());
				Pair<String, String> p = new Pair<String,String>(entry.getKey().getKey(), entry.getKey().getValue());
				tHeap.put(p, set);
			}
			
			for(Map.Entry<String, String> entry:EMG.entrySet()) {
				tEM.put(entry.getKey(), entry.getValue());
			}
			
			
//			heads.add(head);
			//System.out.println("head =  " + head);
			unitStack.put(head, tStack);
			unitHeap.put(head, tHeap);
			unitEM.put(head, tEM);
		}	
		
		
		AllUnits = arg0.getUnits();
//		System.out.println(AllUnits.size()+"HHHHHHH");
//		for(Unit unit:AllUnits) {
////			if(headL.contains(unit)){
////					System.out.println("YES");
////				}
////			else System.out.println("NO");
////			System.out.println("UNIT = " + unit);
//			for(Map.Entry<String, Set<String>> entry1:unitStack.get(unit).entrySet()) {
//				System.out.println(entry1.getKey());
//				System.out.println(entry1.getValue());
//			}
//			System.out.println("HEAP = ");
//			for(Map.Entry<Pair<String,String>, Set<String>> entry1:unitHeap.get(unit).entrySet()) {
//				System.out.println("object = " + entry1.getKey().getKey() + "  field  = " + entry1.getKey().getValue());
//				System.out.println(entry1.getValue());
//			}
//			System.out.println("EMAP");
//			for(Map.Entry<String, String> entry1:unitEM.get(unit).entrySet()) {
//				System.out.println(entry1.getKey() + " - >" + entry1.getValue());
//			}
//		}
		
		
		//System.out.println("exit unitMapCreation");
	}
	
	
	void flow(Unit unit,Pair<SootClass,SootMethod> pair) {
		//System.out.println("enter flow");
		Stmt stmt = (Stmt)unit;
		//System.out.println(stmt);
		visitedNewStmt = Inmap.get(pair).vis;
		objType = Inmap.get(pair).oType; //I have not put objType back in map.get(pair) as the obj is same
		if(stmt instanceof DefinitionStmt) {
			//System.out.println("INSIDE DEFINITION STMT");
			Value lhs = ((DefinitionStmt) stmt).getLeftOp();
			Value rhs = ((DefinitionStmt) stmt).getRightOp();
			if(rhs instanceof NewExpr) {
				//System.out.println("INSIDE NEWEXPR");
				String l = lhs.toString();
				Set<String> set;
				if(!visitedNewStmt.containsKey(unit)) {
					count ++;
					String obj = "R" + count;
					objType.put(obj, rhs.getType());
					//System.out.println(rhs.getType() + "  created obj is  = " + obj);
					visitedNewStmt.put(unit, obj);
				}
				RefType reftype = (RefType)rhs.getType();
				SootClass currentClass = reftype.getSootClass();
				while(currentClass.hasSuperclass() && !currentClass.toString().equals("java.lang.Thread")) {
					currentClass = currentClass.getSuperclass();
				}
				if(currentClass.toString().equals("java.lang.Thread")) {
					EMG.put(visitedNewStmt.get(unit), "E");
					//now change new objs every field to bottom as it is thread obj
					
					Type type = objType.get(visitedNewStmt.get(unit));
					SootClass curr = null;
					if(type instanceof RefType) {
						RefType ref = (RefType)type;
						curr = ref.getSootClass();
						Chain<SootField> chain = curr.getFields();
						Set<SootField> setOfChain = new HashSet<>();
						for(SootField sf:chain) {
							if(sf.getType() instanceof RefLikeType)
								setOfChain.add(sf);
						}
						//System.out.println("CURRENT CLASS = " + currentClass);
						//System.out.println("CHAIN SIZE" + setOfChain.size());
						while(curr.hasSuperclass()) {
							curr = curr.getSuperclass();
							//System.out.println("PARENT CLASS = " + currentClass);
							Chain<SootField> chain2 = curr.getFields();
							for(SootField sf:chain2) {
								if(sf.getType() instanceof RefLikeType)
									setOfChain.add(sf);
							}
						}
						for(SootField sf:setOfChain) {
							Pair<String,String> pairE = new Pair<String,String>(visitedNewStmt.get(unit),sf.getName());
							Set<String> FieldSet = new HashSet<>();
							FieldSet.add("bottom");
							heapG.put(pairE, FieldSet);
						}
					//do not need to check reachability here as the obj is just assigned
					}
				}
				
				set = new HashSet<>();
				set.add(visitedNewStmt.get(unit));
				stackG.put(l, set);
			}
			
			else if(lhs instanceof InstanceFieldRef && !(rhs instanceof InstanceFieldRef)) {
				//x.f = y
//				System.out.println("INSIDE X.f = y");
//				System.out.println("******************" + stmt);
				InstanceFieldRef IFR = (InstanceFieldRef)lhs;
				String l = IFR.getBase().toString();
				String f = IFR.getField().getName();
				String r = rhs.toString();
				if(!stackG.containsKey(l) || !stackG.containsKey(r)) return;
				
				Set<String> setL = stackG.get(l);
				Set<String> setR = stackG.get(r);
				//Set<String> newEscapes = null;
				Set<String> reachable = giveReachable(setR,heapG);
				//System.out.println(giveReachable(setL,heapG));
				if(setL.size() == 1 && setL.iterator().next().equals("bottom")) {
					//newEscapes = new HashSet<>();
					
					for(String str:reachable) {
						EMG.put(str , "E");
						//newEscapes.add(str);
						//System.out.println("::::::::::::::::::::::::::" + str);
					}
					
					
					
					for(String obj:reachable) {
						Type type = objType.get(obj);
						SootClass currentClass = null;
						if(type instanceof RefType) {
							RefType reftype = (RefType)type;
							currentClass = reftype.getSootClass();
							Chain<SootField> chain = currentClass.getFields();
							Set<SootField> setOfChain = new HashSet<>();
							for(SootField sf:chain) {
								if(sf.getType() instanceof RefLikeType)
									setOfChain.add(sf);
							}
							//System.out.println("CURRENT CLASS = " + currentClass);
							//System.out.println("CHAIN SIZE" + setOfChain.size());
							while(currentClass.hasSuperclass()) {
								currentClass = currentClass.getSuperclass();
								//System.out.println("PARENT CLASS = " + currentClass);
								Chain<SootField> chain2 = currentClass.getFields();
								for(SootField sf:chain2) {
									if(sf.getType() instanceof RefLikeType)
										setOfChain.add(sf);
								}
							}
							for(SootField sf:setOfChain) {
								Pair<String,String> pairE = new Pair<String,String>(obj,sf.getName());
								Set<String> FieldSet = new HashSet<>();
								FieldSet.add("bottom");
								heapG.put(pairE, FieldSet);
							}
							
						}

					}
				}
				
				else {//weak update
					for(String str:setL) {
						Pair<String,String> p = new Pair<String,String>(str,f);
						if(heapG.containsKey(p)) {
							Set<String> set = heapG.get(p);
							//System.out.println("H" + set);
							//here set can contain bottom too
							if(set.size() != 1 || !set.iterator().next().equals("bottom")) {
								if(setR.size() == 1 && setR.iterator().next().equals("bottom")) {
									set = new HashSet<>();
									set.add("bottom");
								}
								else {
									set = Sets.union(set , setR);
								}
						
								heapG.put(p, set);
							}
							
						}
						else {//here I am simply pushing setR, not checking anything else
							//System.out.println("N");
							Set<String> set = new HashSet<>();
							//here set is the new set. not setR. so changed in the heap
							set.addAll(setR);
							heapG.put(p, set);
							//System.out.println("heap entries are = ");
//							for(Map.Entry<Pair<String,String>, Set<String>> entry:heapG.entrySet()) {
//								System.out.println(entry.getKey().getKey() + entry.getKey().getValue());
//								System.out.println(entry.getValue());
//							}
						}
					}
					
//					//find out how to find field is static 
//					Set<SootField> staticSetOfField = giveStaticField(pair);
////					newEscapes = new HashSet<>();
//					System.out.println("Static field Reachable");
//					for(SootField sf:staticSetOfField) {
//						if(sf.toString().equals(f)) {	
//							for(String str:reachable) {
//								EMG.put(str , "E");
//								reachable.add(str);
//							}
//							break;
//						}
//					}
					
					//if a object is escaping then all objects reachable from the object is escaping
//					System.out.println("Reachable Objects' field");
					for(String obj:setL) {
						if(EMG.containsKey(obj)) {
							for(String str:reachable) {
								EMG.put(str , "E");
								Type type = objType.get(str);
								SootClass currentClass = null;
								if(type instanceof RefType) {
									RefType reftype = (RefType)type;
									currentClass = reftype.getSootClass();
									Chain<SootField> chain = currentClass.getFields();
									Set<SootField> setOfChain = new HashSet<>();
									for(SootField sf:chain) {
										if(sf.getType() instanceof RefLikeType)
											setOfChain.add(sf);
									}
									//System.out.println("CURRENT CLASS = " + currentClass);
									//System.out.println("CHAIN SIZE" + setOfChain.size());
									while(currentClass.hasSuperclass()) {
										currentClass = currentClass.getSuperclass();
										//System.out.println("PARENT CLASS = " + currentClass);
										Chain<SootField> chain2 = currentClass.getFields();
										for(SootField sf:chain2) {
											if(sf.getType() instanceof RefLikeType)
												setOfChain.add(sf);
										}
									}
									for(SootField sf:setOfChain) {
										Pair<String,String> pairE = new Pair<String,String>(str,sf.getName());
										Set<String> FieldSet = new HashSet<>();
										FieldSet.add("bottom");
										heapG.put(pairE, FieldSet);
									}
									
								}

							}
							break;
						}
					}
//					System.out.println("new escapes =================== " + reachable);
					//if we have bottom , then all objects assigned to it are escaping
					
					//we have all the objects which have just escaped 
					//now we have to make their fields bottom
					//so find all fields of the new objects

					
				}
			}
			
			else if(lhs instanceof StaticFieldRef && !(rhs instanceof InstanceFieldRef)) {
				//B.f = y
//				System.out.println("//////////////////////" + stmt);
				StaticFieldRef SFR = (StaticFieldRef)lhs;
				String f = SFR.getField().getName();
				String r = rhs.toString();
				
				if(!stackG.containsKey(r)) return;
				Set<String> set = stackG.get(r);
				Set<String> reachable = giveReachable(set,heapG);
				for(String str:reachable) {
					EMG.put(str, "E");
				}
				
				for(String obj:reachable) {
					Type type = objType.get(obj);
					SootClass currentClass = null;
					if(type instanceof RefType) {
						RefType reftype = (RefType)type;
						currentClass = reftype.getSootClass();
						Chain<SootField> chain = currentClass.getFields();
						Set<SootField> setOfChain = new HashSet<>();
						for(SootField sf:chain) {
							if(sf.getType() instanceof RefLikeType)
								setOfChain.add(sf);
						}
						//System.out.println("CURRENT CLASS = " + currentClass);
						//System.out.println("CHAIN SIZE" + setOfChain.size());
						while(currentClass.hasSuperclass()) {
							currentClass = currentClass.getSuperclass();
							//System.out.println("PARENT CLASS = " + currentClass);
							Chain<SootField> chain2 = currentClass.getFields();
							for(SootField sf:chain2) {
								if(sf.getType() instanceof RefLikeType)
									setOfChain.add(sf);
							}
						}
						for(SootField sf:setOfChain) {
							Pair<String,String> pairE = new Pair<String,String>(obj,sf.getName());
							Set<String> FieldSet = new HashSet<>();
							FieldSet.add("bottom");
							heapG.put(pairE, FieldSet);
						}
						
					}

				}
			}
			
			else if(!(lhs instanceof InstanceFieldRef) && rhs instanceof InstanceFieldRef) {
				
//				System.out.println("INSIDE  x = y.f");
				if(!(lhs.getType() instanceof RefLikeType)) {
					return;
				}
				String l = lhs.toString();
				InstanceFieldRef IFR = (InstanceFieldRef)rhs;
				String r = IFR.getBase().toString();
				String f = IFR.getField().getName();
				if(!stackG.containsKey(r)) return;
				Set<String> setR = stackG.get(r);
				Set<String> setL = new HashSet<>();
		
				if(setR.size() == 1 && setR.iterator().next().equals("bottom")) {
					setL.add("bottom");
				}
				else {
					for(String str:setR) {
						if(setL.size() == 1 && setL.iterator().next().equals("bottom")) {
							break;
						}
						else {
							Pair<String,String> p = new Pair<String,String>(str,f);
							if(!heapG.containsKey(p)) {
								continue;
							}
							else {
								Set<String> set = heapG.get(p);
								if(set.size() == 1 && set.iterator().next().equals("bottom")) {
									setL = new HashSet<>();
									setL.add("bottom");
								}
								else {
									setL = Sets.union(setL, set);
								}
							}
						}
					}
				}
				
				
				if(setL.size() != 0) {
					stackG.put(l, setL);
				}
			}
			
			
			else if(!(lhs instanceof InstanceFieldRef) && (rhs instanceof StaticFieldRef)) {
				String l = lhs.toString();
				StaticFieldRef SFR = (StaticFieldRef)rhs;
				String f = SFR.getField().getName();
				//System.out.println("(((((((((((((((((((((((" + l +"    " +  SFR +"   "+ f);
				Set<String> set= new HashSet<>();
				set.add("bottom");
				stackG.put(l, set);
			}
			
			
			
			//x = y
			else if(!(lhs instanceof InstanceFieldRef) && !(rhs instanceof InstanceFieldRef) && !(rhs instanceof StaticFieldRef)) {
//				System.out.println("INSIDE  x = y");
				if(!(lhs.getType() instanceof RefLikeType)) {
					return;
				}
				String l = lhs.toString();
				String r = rhs.toString();
				//System.out.println(l + "    " + r);
				Set<String> setL = new HashSet<>();
				if(!stackG.containsKey(r)) return ;
				Set<String> setR = stackG.get(r);
				//System.out.println("HERe");
				setL.addAll(setR);
				stackG.put(l , setL);
				//System.out.println(setL);
				
				//System.out.println("hello");
			}


		}
		else if(stmt.containsInvokeExpr()) {
			InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
			if(expr instanceof VirtualInvokeExpr) {
//				System.out.println(expr + "....................................");
//				System.out.println("INSIDE VIRTUAL INVOKE");
//				System.out.println(expr.getBase().toString() + "  base");
//				System.out.println(expr.getMethod().getName() + "  method");
//				System.out.println(expr.getBase().getType() + "  Type");

				Iterator<Edge> it = cha.edgesOutOf(unit);
				while(it.hasNext()) {
					
					Edge e = it.next();
					SootMethod src = (SootMethod) e.getSrc();
					SootMethod tgtMethod = (SootMethod) e.getTgt();
					SootClass tgtClass = tgtMethod.getDeclaringClass();
					Pair<SootClass , SootMethod> pairToCheck = null;
//					System.out.println("TARGET CLASS = " + tgtClass.getName());
//					System.out.println("TARGET METHOD = " + tgtMethod.getName());

					pairToCheck = new Pair<SootClass , SootMethod>(tgtClass , tgtMethod);
					
					
					if(Inmap.containsKey(pairToCheck)) {
						Set<Unit> invokeSet;
						if(!invokeMap.containsKey(pairToCheck)) {
							invokeSet = new HashSet<>();
							invokeMap.put(pairToCheck, invokeSet);
						}
						invokeSet = invokeMap.get(pairToCheck);
						invokeSet.add(unit);
						invokeMap.put(pairToCheck, invokeSet);
						needToCheck.add(pairToCheck);
						//now I have the target method and its map , I will process it
						Map<Pair<String,String>,Set<String>> targetMethodHeap = Outmap.get(pairToCheck).heap;
						Map<String,String> targetMethodEM = Outmap.get(pairToCheck).emap;
						
						for(Map.Entry<Pair<String,String>, Set<String>> entry:targetMethodHeap.entrySet()) {
							Set<String> tSet = null;
							if(!heapG.containsKey(entry.getKey())) {
								tSet = new HashSet<>();
								heapG.put(entry.getKey(), tSet);
							}
							tSet = heapG.get(entry.getKey());
							tSet.addAll(entry.getValue());
							heapG.put(entry.getKey(), tSet);
						}
						
						for(Map.Entry<String, String> entry:targetMethodEM.entrySet()) {
							EMG.put(entry.getKey(), entry.getValue());
						}
					}
					
					
					
					
					
					

//					System.out.println(needToCheck);
				}
			}
			
//			else if(expr instanceof )
		}
		
		
		else if(stmt instanceof ReturnVoidStmt) {
			//System.out.println("hello");
			setOfReturns.add(unit);
		}
		
		else if(stmt instanceof EnterMonitorStmt) {
			//System.out.println(stmt + "is in enter monitor");
//			Value v = ((EnterMonitorStmt) unit).getOp();
			Pair<String,String> pairName = new Pair<String,String>(pair.getKey().getName(),pair.getValue().getName());
			syncMap.put(pairName, unit);
		}
		
		else if(stmt instanceof ExitMonitorStmt) {
			//System.out.println(stmt + "is in exit monitor");
		}
		
		else if(stmt instanceof ThrowStmt) {
			setOfReturns.add(unit);
		}
		
//		System.out.println("exit flow");
	}
	
	void analyze(Pair<SootClass,SootMethod> pair) {
//		System.out.println("enter analyze");
//		System.out.println(pair.getKey().getName());
//		System.out.println(pair.getValue().getName());
		Body arg0 = pair.getValue().getActiveBody();
		//System.out.println(arg0);
		stackG = null;
		heapG = null;
		EMG = null;
		finalstackG = new HashMap<>();;
		finalheapG = new HashMap<>();
		finalEMG = new HashMap<>();
		setOfReturns = new HashSet<>();
		invokeMap = new HashMap<>();
		needToCheck = new HashSet<>();
		
		BriefUnitGraph cfg = new BriefUnitGraph(arg0); 
		
		

		PatchingChain<Unit> AllUnits = arg0.getUnits();
		Set<Unit> workListPerMethod = new HashSet<Unit>();
		for(Unit unit:AllUnits) {
			workListPerMethod.add(unit);
		}
		
		/////////////////////////////////////////////////////////////////////////
		
//		Map<Unit,Map<String,Set<String>>> stack = new HashMap<>();
//		Map<Unit,Map<Pair<String,String>,Set<String>>> heap = new HashMap<>();
//		Map<Unit,Map<String,String>> EM = new HashMap<>();
		/////////////////////////////////////////////////////////////////////////
		
		

		while(workListPerMethod.size() != 0) {
//			System.out.println("INSIDE WORK LIST PER METHOD");
//			//printing the worklistpermethod
//			System.out.println(workListPerMethod);
			
			Unit currUnit = workListPerMethod.iterator().next();
			workListPerMethod.remove(currUnit);
			Stmt currstmt = (Stmt)currUnit;
			if(currstmt instanceof InvokeStmt || currstmt instanceof DefinitionStmt || currstmt instanceof ReturnVoidStmt || currstmt instanceof ReturnStmt || currstmt instanceof GotoStmt|| currstmt instanceof IfStmt || currstmt instanceof NopStmt || currstmt instanceof EnterMonitorStmt  || currstmt instanceof ExitMonitorStmt || currstmt instanceof ThrowStmt) {
				//System.out.println("CURRENT STATEMENT = " + currstmt);
				Map<String,Set<String>> oldstackOfCurr = unitStack.get(currUnit);
				Map<Pair<String,String>,Set<String>> oldheapOfCurr = unitHeap.get(currUnit);
				Map<String,String> oldEMOfCurr = unitEM.get(currUnit);
				
				Map<String,Set<String>> newstackOfCurr = new HashMap<>();
				Map<Pair<String,String>,Set<String>> newheapOfCurr = new HashMap<>();
				Map<String,String> newEMOfCurr = new HashMap<>();
				
				List<Unit> predsList = cfg.getPredsOf(currUnit);
				
				
				for(Unit predOfUnit:predsList) {
					//if(heads.contains(predOfUnit)) continue;
					//System.out.println("INSIDE THE LOOP 1");
					Stmt predstmt = (Stmt)predOfUnit;
//					System.out.println("PRED IS = " + predOfUnit);
					if(predstmt instanceof DefinitionStmt || predstmt instanceof InvokeStmt || predstmt instanceof ReturnVoidStmt || predstmt instanceof ReturnStmt|| predstmt instanceof GotoStmt|| predstmt instanceof IfStmt || predstmt instanceof NopStmt || predstmt instanceof EnterMonitorStmt || predstmt instanceof ExitMonitorStmt || predstmt instanceof ThrowStmt) {
//						System.out.println("INSIDE THE FIRST IF AND THE PRED IS =  " + predstmt);
						Map<String,Set<String>> stackOfPred = unitStack.get(predOfUnit);
						Map<Pair<String,String>,Set<String>> heapOfPred = unitHeap.get(predOfUnit);
						Map<String,String> EMOfPred = unitEM.get(predOfUnit);
						
						//stack join
						if(stackOfPred != null) {
							for(Map.Entry<String,Set<String>> entry:stackOfPred.entrySet()) {
								String predkey = entry.getKey();
								Set<String> predset = entry.getValue();
								if(predset.size() == 1 && predset.iterator().next().equals("bottom")) {
									Set<String> newset = new HashSet<>();
									newset.add("bottom");
									newstackOfCurr.put(predkey, newset);
								}
								else if(newstackOfCurr.containsKey(predkey)) {
									Set<String> newset = newstackOfCurr.get(predkey);
									if(newset.size() != 1|| !newset.iterator().next().equals("bottom")) {
										newset = Sets.union(newset, predset);
										newstackOfCurr.put(predkey, newset);
									}
								}
								else {
									Set<String> newset = new HashSet<>();
									newset.addAll(predset);
									newstackOfCurr.put(predkey, newset);
								}
							}
						}
						
						
						//heap join
						if(heapOfPred != null) {
							for(Map.Entry<Pair<String,String>,Set<String>> entry:heapOfPred.entrySet()) {
								Pair<String,String> predkey = entry.getKey();
								Set<String> predset = entry.getValue();
								if(predset.size() == 1 && predset.iterator().next().equals("bottom")){
									Set<String> newset = new HashSet<>();
									newset.add("bottom");
									newheapOfCurr.put(predkey, newset);
								}
								else if(newheapOfCurr.containsKey(predkey)) {
									Set<String> newset = newheapOfCurr.get(predkey);
									if(newset.size() != 1|| !newset.iterator().next().equals("bottom")) {
										newset = Sets.union(newset, predset);
										newheapOfCurr.put(predkey, newset);
									}
								}
								else {
									Set<String> newset = new HashSet<>();
									newset.addAll(predset);
									newheapOfCurr.put(predkey, newset);
								}
								
							}

						}
						
						
						//EM join
						if(EMOfPred != null) {
							for(Map.Entry<String, String> entry:EMOfPred.entrySet()) {
								String key = entry.getKey();
								String val = entry.getValue();
								newEMOfCurr.put(key, val);
							}
						}
						
						
						
						stackG = newstackOfCurr;
						heapG = newheapOfCurr;
						EMG = newEMOfCurr;
						flow(currUnit,pair);
						newstackOfCurr = stackG;
						newheapOfCurr = heapG;
						newEMOfCurr = EMG;
						
						
						if(!newstackOfCurr.equals(oldstackOfCurr) || !newheapOfCurr.equals(oldheapOfCurr) || !newEMOfCurr.equals(oldEMOfCurr)) {
							unitStack.put(currUnit, newstackOfCurr);
							unitHeap.put(currUnit, newheapOfCurr);
							unitEM.put(currUnit, newEMOfCurr);
							workListPerMethod.addAll(cfg.getSuccsOf(currUnit));
						}
					}
				}
			}
		}
		
		
		//now I will check the set of returns
		
		for(Unit unit:setOfReturns) {
			stackG = unitStack.get(unit);
			heapG = unitHeap.get(unit);
			EMG = unitEM.get(unit);
			//System.out.println(stackG.size());
			//System.out.println(heapG.size());
			//System.out.println("IN RETURN BLOCK");
			for(Map.Entry<String, Set<String>> entry:stackG.entrySet()) {
				String key = entry.getKey();
				Set<String> set = entry.getValue();
				if(set.size() == 1 && set.iterator().next().equals("bottom")) {
					Set<String> newset = new HashSet<>();
					newset.add("bottom");
					finalstackG.put(key, newset);
				}
				else if(finalstackG.containsKey(key)) {
					Set<String> newset = finalstackG.get(key);
					if(newset.size() != 1 || !newset.iterator().next().equals("bottom")) {
						newset = Sets.union(newset, set);
						finalstackG.put(key, newset);
					}
				}
				else {
					Set<String> newset = new HashSet<>();
					newset.addAll(set);
					finalstackG.put(key, newset);
				}
			}
			for(Map.Entry<Pair<String,String>,Set<String>> entry:heapG.entrySet()) {
				Pair<String,String> key = entry.getKey();
				Set<String> set = entry.getValue();
				if(set.size() == 1 && set.iterator().next().equals("bottom")){
					Set<String> newset = new HashSet<>();
					newset.add("bottom");
					finalheapG.put(key, newset);
				}
				else if(finalheapG.containsKey(key)) {
					Set<String> newset = finalheapG.get(key);
					if(newset.size() != 1 || !newset.iterator().next().equals("bottom")) {
						newset = Sets.union(newset, set);
						finalheapG.put(key, newset);
					}
				}
				else {
					Set<String> newset = new HashSet<>();
					newset.addAll(set);
					finalheapG.put(key, newset);
				}
			}
			
			for(Map.Entry<String, String> entry:EMG.entrySet()) {
				finalEMG.put(entry.getKey(),entry.getValue());
			}
		}
		
		stackG = Outmap.get(pair).stack;
		heapG = Outmap.get(pair).heap;
		EMG = Outmap.get(pair).emap;
		
		
		
		/////////////////////////////////////////////////////
		//calling its caller if EM and heap do not match
		
		if(!finalheapG.equals(heapG) || !finalEMG.equals(EMG)) {
			Iterator<Edge> edgeinto = cha.edgesInto(pair.getValue());
			while(edgeinto.hasNext()) {
				Edge e = edgeinto.next();
				SootMethod method = (SootMethod) e.getSrc();
				SootClass cls = method.getDeclaringClass();
				Pair<SootClass , SootMethod> pair1 = new Pair<SootClass , SootMethod>(cls,method);
				if(Inmap.containsKey(pair1)) {
					workList.add(pair1);
				}
			}
		}
		Outmap.get(pair).stack = finalstackG;
		Outmap.get(pair).heap = finalheapG;
		Outmap.get(pair).emap = finalEMG;
		
		//////////////////////////////////////////////////////
		
		for(Pair<SootClass,SootMethod> pairToCheck:needToCheck) {
			Set<String> formalParams = null;
			formalParams = new HashSet<>();
			
//			Body arg1 = pairToCheck.getValue().getActiveBody();
//			
//			List<Local> listOfParams = arg1.getParameterLocals();
			
//			for(Local l:listOfParams) {
//				System.out.println(l.toString());
//				if(l.getType() instanceof RefLikeType) {
//					formalParams.add(l.toString());
//				}
//			}
			
			
			//System.out.println(pairToCheck.getKey()+  "     " + pairToCheck.getValue());
			formalParams.add("this");
			Map<String,Set<String>> stackOld = Inmap.get(pairToCheck).stack;
			Map<Pair<String,String>,Set<String>> heapOld = Inmap.get(pairToCheck).heap;
			Map<String,String> EMOld = Inmap.get(pairToCheck).emap;
			

			Map<String,Set<String>> tStack = new HashMap<>();
			Map<Pair<String,String>,Set<String>> tHeap = new HashMap<>();
			Map<String,String> tEM = new HashMap<>();
			
			if(stackOld != null) {
				for(Map.Entry<String, Set<String>> entry:stackOld.entrySet()) {
					Set<String> set = new HashSet<>();
					set.addAll(entry.getValue());
					tStack.put(entry.getKey(), set);
				}
			}
			
			if(heapOld != null) {
				for(Map.Entry<Pair<String,String>,Set<String>> entry:heapOld.entrySet()) {
					Set<String> set = new HashSet<>();
					set.addAll(entry.getValue());
					Pair<String, String> p = new Pair<String,String>(entry.getKey().getKey(), entry.getKey().getValue());
					tHeap.put(p, set);
				}
			}
			
			if(EMOld != null) {
				for(Map.Entry<String, String> entry:EMOld.entrySet()) {
					tEM.put(entry.getKey(), entry.getValue());
				}
			}
			
			
			
			Set<Unit> UnitInvoke = invokeMap.get(pairToCheck);
			for(Unit unit:UnitInvoke) {
				stackG = unitStack.get(unit);
				heapG = unitHeap.get(unit);
				EMG = unitEM.get(unit);
				
				Stmt stmt = (Stmt)unit;
				InstanceInvokeExpr expr = (InstanceInvokeExpr)stmt.getInvokeExpr();
				String base = expr.getBase().toString();
				Set<String> set = stackG.get(base);
				Set<String> tset = tStack.get("this");
				tset.addAll(set);
				tStack.put("this", tset);//updating the this in the target method
				//stack updation complete
				//heap updation start
				Set<String> reach = giveReachable(set , heapG);//this line is there as the rule states 
				if(reach.size() == 1 && reach.iterator().next().equals("bottom")) {
					for(Map.Entry<Pair<String,String>, Set<String>> entry:heapG.entrySet()) {
						Set<String> setH = entry.getValue();
						Set<String> tset1 = null;
						if(!tHeap.containsKey(entry.getKey())) {
							tset1 = new HashSet<>();
							tHeap.put(entry.getKey(), tset1);
						}
						tset1 = tHeap.get(entry.getKey());
						tset1.addAll(setH);
						tHeap.put(entry.getKey(),tset1);
					}
					
					
					for(Map.Entry<String, String> entry:EMG.entrySet()) {
						tEM.put(entry.getKey(), entry.getValue());
					}
				}
				else {
					for(String obj:reach) {
						Type type = objType.get(obj);
						SootClass currentClass = null;
						if(type instanceof RefType) {
							RefType reftype = (RefType)type;
							currentClass = reftype.getSootClass();
							Chain<SootField> chain = currentClass.getFields();
							Set<SootField> setOfChain = new HashSet<>();
							for(SootField sf:chain) {
								if(sf.getType() instanceof RefLikeType)
									setOfChain.add(sf);
							}
							//System.out.println("CURRENT CLASS = " + currentClass);
							//System.out.println("CHAIN SIZE" + setOfChain.size());
							while(currentClass.hasSuperclass()) {
								currentClass = currentClass.getSuperclass();
								//System.out.println("PARENT CLASS = " + currentClass);
								Chain<SootField> chain2 = currentClass.getFields();
								for(SootField sf:chain2) {
									if(sf.getType() instanceof RefLikeType)
										setOfChain.add(sf);
								}
							}
							
							for(SootField f:setOfChain) {
								Pair<String,String> p = new Pair<String,String>(obj,f.getName());
								if(heapG.containsKey(p)) {
									Set<String> set1;
									if(!tHeap.containsKey(p)) {
										set1 = new HashSet<>();
										tHeap.put(p, set1);
									}
									set1 = tHeap.get(p);
									set1.addAll(heapG.get(p));
									tHeap.put(p, set1);
								}
							}
						}
					}
					
					
					for(String obj:reach) {
						if(EMG.containsKey(obj)) {
							tEM.put(obj, "E");
						}
					}
				}
			
			
				
			}

			if(!stackOld.equals(tStack) || !heapOld.equals(tHeap) || !EMOld.equals(tEM)) {
				Inmap.get(pairToCheck).stack = tStack;
				Inmap.get(pairToCheck).heap = tHeap;
				Inmap.get(pairToCheck).emap = tEM;
				workList.add(pairToCheck);
			}
		}
		
		
//		System.out.println("exit analyze");
		
	}
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 */
//		System.out.println("hello");
		cha = Scene.v().getCallGraph();
		syncMap = new HashMap<>();
//		Set<MethodOrMethodContext> s = new HashSet<>();
//		Iterator<MethodOrMethodContext> it = cha.sourceMethods();
//		while (it.hasNext()) {
//		    MethodOrMethodContext e = it.next();
//		    s.add(e);
//		}
		
		
//		Iterator<MethodOrMethodContext> iit = s.iterator();
//		while(iit.hasNext()) {
//			System.out.println(iit.next());
//		}
		
       
		
		
         
         
		count = 0;
		Inmap = new HashMap<>();
		Outmap = new HashMap<>();
		visitedNewStmt = new HashMap<>();
		objType = new HashMap<>();
		Chain<SootClass> classes = Scene.v().getApplicationClasses();
		Set<SootClass> classSet = new HashSet<>();
		Set<Pair<SootClass , SootMethod>> setOfMethods = new HashSet<>();
		// Iterate over the classes and print their names
		for (SootClass cls : classes) {
		    if(!cls.getName().startsWith("jdk")) {
		    	classSet.add(cls);
		    	List<SootMethod> list = cls.getMethods();
		    	Iterator<SootMethod> methodIterator = list.iterator();
		    	while(methodIterator.hasNext()) {
		    		Pair<SootClass , SootMethod> pair = new Pair<SootClass , SootMethod>(cls , methodIterator.next());
		    		setOfMethods.add(pair);
		    		
		    	}
		    }
		}
		
//		System.out.println("hello" + setOfMethods);
		for(Pair<SootClass , SootMethod> pair:setOfMethods) {
//			System.out.println(pair.getKey().toString() + "     " + pair.getValue().getName());
			mapCreation(pair);
			
		}
		
		
		
		//creation of GlobalUnitStack GlobalUnitHeap GlobalUnitEM
		//I am just creating three objects , and after analyzing I have just put the pair<SootClass,SootMethod> and the unitStack,unitHeap,unitEM
		//as they are of current method so they are fresh.everytime the method  is analyzed the fresh values are put. so after the whole thing
		//stops , I have the recent unit stacks , unit heaps and unit EM.
		GlobalUnitStack = new HashMap<>();
		GlobalUnitHeap = new HashMap<>();
		GlobalUnitEM = new HashMap<>();
		
		
		workList = new HashSet<>();
		
		
		
		//taking main method like this
		SootMethod mainMethod = null;
//		System.out.println(setOfMethods);
		for(Pair<SootClass,SootMethod> pair:setOfMethods) {
			if(pair.getValue().getName().equals("main")) {
				mainMethod = pair.getValue();
			}
		}

//		System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
//		Iterator<Edge> e = cha.edgesOutOf(mainMethod);
//		
//		//checking the thread edges type
//		while(e.hasNext()) {
//			System.out.println(e.next());
//		}
		Pair<SootClass,SootMethod> main = new Pair<SootClass,SootMethod>(mainMethod.getDeclaringClass(),mainMethod);
		workList.add(main);
//		System.out.println("+++++++++++++++++++++++++++++++++++++++++++++++");
		while(workList.size() != 0) {
//			System.out.println("_____________________________________________");
			Pair<SootClass,SootMethod> pair = workList.iterator().next();
//			System.out.println("in internalTransform");
//			System.out.println(pair.getKey().getName());
//			System.out.println(pair.getValue().getName());
			workList.remove(pair);
			unitMapCreation(pair);
			
			analyze(pair);
			
			//update GlobalUnitStack,GlobalUnitHeap,GlobalUnitEM
			Pair<String,String> pairName = new Pair<String,String>(pair.getKey().getName(),pair.getValue().getName());
			GlobalUnitStack.put(pairName, unitStack);
			GlobalUnitHeap.put(pairName, unitHeap);
			GlobalUnitEM.put(pairName, unitEM);
			//finished 
			
//			System.out.println("AFTER ANALYZING THE FUNCTION WORKLIST IS = ");
//			System.out.println(workList);
//			System.out.println("====================INSIDE========================");
			
			
//			for(Map.Entry<Pair<SootClass,SootMethod>, DS> entry:Inmap.entrySet()) {
//				System.out.println("---------------------------------------------------");
//				System.out.println(entry.getKey().getKey().getName() + "   " + entry.getKey().getValue().getName());
//				System.out.println("STACK = ");
//				for(Map.Entry<String, Set<String>> entry1:entry.getValue().stack.entrySet()) {
//					System.out.println(entry1.getKey());
//					System.out.println(entry1.getValue());
//				}
//				System.out.println("HEAP = ");
//				for(Map.Entry<Pair<String,String>, Set<String>> entry1:entry.getValue().heap.entrySet()) {
//					System.out.println("object = " + entry1.getKey().getKey() + "  field  = " + entry1.getKey().getValue());
//					System.out.println(entry1.getValue());
//				}
//				System.out.println("EMAP");
//				for(Map.Entry<String, String> entry1:entry.getValue().emap.entrySet()) {
//					System.out.println(entry1.getKey() + " - >" + entry1.getValue());
//				}
//			}

			
//			for(Map.Entry<Pair<SootClass,SootMethod>, DS> entry:Outmap.entrySet()) {
//				System.out.println("---------------------------------------------------");
//				System.out.println(entry.getKey().getKey().getName() + "   " + entry.getKey().getValue().getName());
//				System.out.println("STACK = ");
//				for(Map.Entry<String, Set<String>> entry1:entry.getValue().stack.entrySet()) {
//					System.out.println(entry1.getKey());
//					System.out.println(entry1.getValue());
//				}
//				System.out.println("HEAP = ");
//				for(Map.Entry<Pair<String,String>, Set<String>> entry1:entry.getValue().heap.entrySet()) {
//					System.out.println("object = " + entry1.getKey().getKey() + "  field  = " + entry1.getKey().getValue());
//					System.out.println(entry1.getValue());
//				}
//				System.out.println("EMAP");
//				for(Map.Entry<String, String> entry1:entry.getValue().emap.entrySet()) {
//					System.out.println(entry1.getKey() + " - >" + entry1.getValue());
//				}
//			}

		}
		//System.out.println("hello");
		
		//printing the map
		
		
//		System.out.println("===================FINAL PRINTING========================");
//		for(Map.Entry<Pair<SootClass,SootMethod>, DS> entry:Outmap.entrySet()) {
//			System.out.println("---------------------------------------------------");
//			System.out.println(entry.getKey().getKey().getName() + "   " + entry.getKey().getValue().getName());
//			System.out.println("STACK = ");
//			for(Map.Entry<String, Set<String>> entry1:entry.getValue().stack.entrySet()) {
//				System.out.println(entry1.getKey());
//				System.out.println(entry1.getValue());
//			}
//			System.out.println("HEAP = ");
//			for(Map.Entry<Pair<String,String>, Set<String>> entry1:entry.getValue().heap.entrySet()) {
//				System.out.println("object = " + entry1.getKey().getKey() + "  field  = " + entry1.getKey().getValue());
//				System.out.println(entry1.getValue());
//			}
//			System.out.println("EMAP");
//			for(Map.Entry<String, String> entry1:entry.getValue().emap.entrySet()) {
//				System.out.println(entry1.getKey() + " - >" + entry1.getValue());
//			}
//		}
		
//		System.out.println("hello");
//		for(Map.Entry<Pair<String,String>, Unit> entry:syncMap.entrySet()) {
//			System.out.println(entry.getKey().getKey() + "    " + entry.getKey().getValue());
//			System.out.println(entry.getValue());
//		}
		//now write to the answer
		
		for(int i = 0;i < A2.queryList.size();i ++) {
			EscapeQuery q = A2.queryList.get(i);
			String ClassName = q.getClassName();
			String MethodName = q.getMethodName();
			//System.out.println(ClassName);
			//System.out.println(MethodName);
			
			Pair<String,String> pairName = new Pair<String,String>(ClassName,MethodName);
			Unit unit = syncMap.get(pairName);
			//System.out.println(unit);
			Value v = ((EnterMonitorStmt) unit).getOp();
			Set<String> set1 = GlobalUnitStack.get(pairName).get(unit).get(v.toString());
			//System.out.println(set1.size());
			for(String str:set1) {
				//System.out.println(str);
				if(GlobalUnitEM.get(pairName).get(unit).containsKey(str)) {
					A2.answers[i] = "No";
					break;
				}
			}
			//System.out.println("hello");
			 if(set1.size() == 1 && set1.iterator().next().equals("bottom")) {
				// System.out.print("jj");
				 A2.answers[i] = "No";
				 
			 }
			 else if(A2.answers[i] == null){
				 A2.answers[i] = "Yes";
			 }
			
		}
		
		
		//System.out.println("END");
	}

	
}