module SoSPackage

using JuMP, Mosek, SCS

export SoSProblem, setOptions, showOptions,
       setObjective, setParameters, addConstraint, removeConstraint,
       buildSoS, solve, getObjectiveValue, getSolution, getDualSolution

include("polynomial.jl")

type SoSProblem
    m :: Model
    maxDeg :: Int
    maxVarInd :: Int 
    objective :: Polynomial 
    constraints :: Array{Polynomial,1}
    options :: Dict{Any,Any}

    SoSProblem(m,d,n,obj,cons,opt) = (d < 1 || n < 1) ? error("Parameters must be positive.") : new(m,d,n,obj,cons,opt)
end

function SoSProblem(n::Int, d::Int)
    SoSProblem(Model(solver=MosekSolver(QUIET=true)), 2*ceil(d/2), n,
        Polynomial(), Array{Polynomial,1}(0),
        Dict{Any,Any}(:quiet=>true, :solver=>"mosek", :sense=>"min", :prec=>"medium"))
end

function setParameters(obj::SoSProblem,n::Int,d::Int)
    obj.maxDeg = d
    obj.maxVarInd = n
end

showOptions(obj::SoSProblem) = println(obj.options)
function setOptions(obj::SoSProblem;quiet=true, solver="mosek", sense="min", prec="medium")
    obj.options[:prec]=prec
    if prec == "medium"
        epsilon = 1e-8
    elseif prec == "high"
        epsilon = 1e-10
    elseif prec == "low"
        epsilon = 1e-6
    elseif prec == "minimum"
        epsilon = 1e-4
    end
    if solver == "mosek"
        obj.m.solver = MosekSolver(QUIET=quiet,
            INTPNT_CO_TOL_DFEAS=epsilon, INTPNT_CO_TOL_PFEAS=epsilon,
            INTPNT_CO_TOL_REL_GAP=10*epsilon)
    elseif solver == "SCS"
        epsilon ^= (1/2)
        obj.m.solver = SCSSolver(verbose=(!quiet), eps=epsilon, max_iters=20000)
    else
        error("Not a compatible solver.")
    end
    obj.options[:solver]=solver
    obj.options[:quiet]=quiet
    
    obj.options[:sense]=sense
    JuMP.setobjectivesense(obj.m, (sense == "min") ? :Min : :Max) 
end

function setObjective(obj::SoSProblem, p::Polynomial)
    if deg(p) > obj.maxDeg || maxVarInd(p) > obj.maxVarInd
        error("Out of range.")
    end
    obj.objective = p;
end

function addConstraint(obj::SoSProblem, p::Polynomial)
    if deg(p) > obj.maxDeg || maxVarInd(p) > obj.maxVarInd
        error("Out of range.")
    end
    push!(obj.constraints, p)
end

removeConstraint(obj::SoSProblem) = empty!(obj.constraints)
function removeConstraint(obj::SoSProblem, L::Array{Int,1})
    k = length(obj.constraints)
    b = ones(Bool,k)
    b[L] = 0
    obj.constraints = obj.constraints[b]
end

function makeProdTables(n::Int,d::Int)
    nHk = [ binomial(n+i-1,i) for i=1:d ]
    prodtables = Array{Array{Int,2},2}(d-1,d-1)
    for d1=1:d-1, d2=1:d-1
        if d1+d2>d continue end
        if d1>d2 
            prodtables[d1,d2]=prodtables[d2,d1]'
        else
            prodtables[d1,d2]=Array{Int,2}(nHk[d1],nHk[d2])
            for i=1:nHk[d1], j=1:nHk[d2]
                m = computeColexind(munion(computeMultiset(d1,i),computeMultiset(d2,j)))
                prodtables[d1,d2][i,j]=m[2]
            end
        end
    end
    prodtables
end

function buildConstraint(n::Int, d::Int, q::Polynomial, prodtables::Array{Array{Int,2},2})
    coeffmat = sort(collect(q.coeffs))
    sp = length(coeffmat)
    D = d - deg(q)
    nHk = [ binomial(n+i-1,i) for i=1:d ]
    nHllk = [ 1+sum(nHk[1:i]) for i=0:d ]
    numconstr = nHllk[D+1]

    I = zeros(Int, sp, numconstr)
    J = zeros(Int, sp, numconstr)
    V = [coeffmat[i][2] for i=1:sp]
    I[:,1] = [coeffmat[i][1][1] for i=1:sp]
    J[:,1] = [coeffmat[i][1][2] for i=1:sp]
    for i=1:sp, d2=1:D
        d1, colex1 = coeffmat[i][1]
        I[i,nHllk[d2]+1:nHllk[d2+1]] = d1+d2
        if d1 == 0
            J[i,nHllk[d2]+1:nHllk[d2+1]] = 1:nHk[d2]
        else
            J[i,nHllk[d2]+1:nHllk[d2+1]] = prodtables[d1,d2][colex1,1:nHk[d2]]
        end
    end
    I,J,V
end

function buildSoS(obj::SoSProblem)
    println("Building...")
    n, d = obj.maxVarInd, obj.maxDeg
    nHk = [ binomial(n+i-1,i) for i=1:d ]
    nHllk = [ 1+sum(nHk[1:i]) for i=0:d ]
    N = nHllk[div(d,2)+1]
    #@variable(obj.m, Y[1:N,1:N], SDP)
    #@constraint(obj.m, Y[1,1]==1)
    Y = zeros(AffExpr, N,N)
    Y[1,1] = 1.0
    @variable(obj.m, moments[i=1:d,j=1:nHk[i]])
    prodtables = makeProdTables(n, d)
    
    for i=1:div(d,2), j=1:nHk[i]
        ind1 = nHllk[i]+j
        #@constraint(obj.m, Y[1,ind1]==moments[i,j])
        Y[1,ind1] += moments[i,j]
        Y[ind1,1] += moments[i,j]
        for k=1:div(d,2), l=1:nHk[k]
            ind2 = nHllk[k]+l
            colex = prodtables[i,k][j,l]
            #(ind1 <= ind2) && @constraint(obj.m, Y[ind1,ind2]==moments[i+k,colex])
            Y[ind1,ind2] += moments[i+k,colex]
        end
    end
    @SDconstraint(obj.m, Y >= 0)
    
    for q in obj.constraints
        I,J,V = buildConstraint(n, d, q, prodtables)
        dim1, dim2 = size(I)
        for j=1:dim2
            if I[1,j] == 0
                @constraint(obj.m, V[1]+sum{V[i]*moments[I[i,j],J[i,j]], i=2:dim1} == 0)
            else
                @constraint(obj.m, sum{V[i]*moments[I[i,j],J[i,j]], i=1:dim1} == 0)
            end
        end
    end
    show(obj.m)
    println()
end

function buildObjective(obj::SoSProblem)
    p = obj.objective
    constterm = get(p.coeffs, (0,1), 0)
    coeffmat = sort(collect(p.coeffs))
    coeffmat[1][1][1] == 0 && shift!(coeffmat)
    sp = length(coeffmat)
    #println(coeffmat)
    var1 = getvariable(obj.m, :moments)
    if (obj.options[:sense]=="min")
        @objective(obj.m, :Min, constterm+sum{coeffmat[i][2]*var1[coeffmat[i][1][1], coeffmat[i][1][2]], i=1:sp})
    else
        @objective(obj.m, :Max, constterm+sum{coeffmat[i][2]*var1[coeffmat[i][1][1], coeffmat[i][1][2]], i=1:sp})
    end
end

function solve(obj::SoSProblem)
    buildObjective(obj)
    status = JuMP.solve(obj.m)
    status
end

getObjectiveValue(obj::SoSProblem) = getobjectivevalue(obj.m)
function getSolution(obj::SoSProblem)
    var1 = getvariable(obj.m, :moments)
    sol1 = getvalue(var1)
    sol1mat = zeros(length(keys(sol1)),3)
    sol1mat[:,1] = [k[1] for k in keys(sol1)]
    sol1mat[:,2] = [k[2] for k in keys(sol1)]
    sol1mat[:,3] = [sol1[k[1],k[2]] for k in keys(sol1)]
    sol1mat
end

function getSolution(obj::SoSProblem, d::Int)
    n = obj.maxVarInd
    nHd = binomial(n+d-1, d)
    var1 = getvariable(obj.m, :moments)
    sol1 = getvalue(var1)
    #println(sol1)
    soldegd = zeros(nHd)
    for i=1:nHd
        soldegd[i] = sol1[d, i]
    end
    soldegd
end

function getDualSolution(obj::SoSProblem)
    var1 = getvariable(obj.m, :Y)
    sol1 = getdual(var1)
    N = maximum([ k[1] for k in keys(sol1) ])
    sol1mat = zeros(N,N)
    for k in keys(sol1)
        sol1mat[k[1],k[2]] = sol1[k[1],k[2]]
    end
    sol1mat
end



end
