import Base: +,-,.*,*,convert,dot,zero,zeros    #methods to overload

export Polynomial

immutable Polynomial
    coeffs::Dict{Tuple{Int,Int},Number}

    Polynomial{T<:Number}(c::T)=new(Dict((0,1)=>c))
    Polynomial{T<:Number}(coeffs::Dict{Tuple{Int,Int},T})=new(coeffs)
    Polynomial() = new(Dict((0,1)=>0.0))
end

Polynomial(a::Int,b::Int) = (a > 0 && b >= 0) ? Polynomial(Dict((a,b)=>1.0)) : error("Parameter out of range.")
function Polynomial(expvec::Array{Int,1})
    d, colexind = computeColexind(expvec)
    Polynomial(d, colexind)
end
deg(p::Polynomial) = maximum([ m[1] for m in keys(p.coeffs) ])
maxVarInd(p::Polynomial) = maximum([ maxVarInd(m[1],m[2]) for m in keys(p.coeffs) ])
function maxVarInd(d::Int, colexind::Int)
    m = 1
    while (colexind < binomial(m+d-1,d)) m+=1 end
    return m
end

function computeColexind(expvec::Array{Int,1})
    I = find(expvec)
    V = expvec[I]
    d = sum(V)

    if d == 0 colexind = 1
    else
        #Convert multiset to set
        I2 = zeros(Int,d)
        temp = 0
        for i=1:length(I)
            I2[temp+1:temp+V[i]] = I[i]
            temp += V[i]
        end
        I2 = I2+collect(0:d-1)
        
        #Compute colex_index of set 
        colexind = 1
        for i=1:d
            if I2[i]-1 >= i
                colexind += binomial(I2[i]-1,i)
            end
        end
    end
    d, colexind
end

function computeMultiset(d::Int, colexind::Int)
    if d==0
        return Array{Int,1}(0)
    end
    #Convert colex_ind to a set
    J = zeros(Int,d)
    for i=d:-1:1
        j = i
        while colexind > binomial(j, i)
            j += 1
        end
        if j-1 >= i
            colexind -= binomial(j-1,i)
        end
        J[i] = j
    end

    #Convert set to multiset
    J = J-collect(0:d-1);
    I = zeros(Int,J[end]);
    for i=1:length(J)
        I[J[i]]+=1
    end
    I
end

function munion(vec1::Array{Int,1},vec2::Array{Int,1})
    l1, l2 = length(vec1), length(vec2)
    vec = zeros(Int, max(l1, l2))
    vec[1:l1] += vec1
    vec[1:l2] += vec2
    vec
end

zero(::Polynomial)=Polynomial()
function zeros(::Type{Polynomial},m::Int)
    if m < 0 error("Dimension must be positive.") end
    v = Array{Polynomial,1}(m)
    for i=1:m
        v[i] = Polynomial()
    end
    v
end
function zeros(::Type{Polynomial},m::Int,n::Int)
    if (m < 0 || n < 0) error("Dimension must be positive.") end
    v = Array{Polynomial,2}(m,n)
    for i=1:m
        for j=1:n
            v[i,j] = Polynomial()
        end
    end
    v
end 

function dictadd{S<:Any,T<:Number}(dict1::Dict{S,T},dict2::Dict{S,T})
    dict = Dict{S,T}()
    for key in keys(dict1)
        dict[key] = dict1[key]
    end
    for key in keys(dict2)
        if haskey(dict, key) dict[key]+=dict2[key]
        else dict[key] = dict2[key]
        end
    end    
    filter!(( (x,y)->y!=0 ), dict)
    return dict
end

+{S<:Number}(p::Polynomial,c::S)=+(p,Polynomial(c))
+{S<:Number}(c::S,p::Polynomial)=+(p,Polynomial(c))
function +(p1::Polynomial,p2::Polynomial)
    coeff1, coeff2 = p1.coeffs, p2.coeffs
    coeff = dictadd(coeff1,coeff2)
    Polynomial(coeff)
end

-(p::Polynomial)=(-1.0)*p
-(p1::Polynomial,p2::Polynomial)=p1+(-1.0)*p2
-{S<:Number}(p::Polynomial,c::S)=p+(-1.0)*c
-{S<:Number}(c::S,p::Polynomial)=c+(-1.0)*p


function dictmul{S<:Any,T<:Number}(dict1::Dict{S,T},c::T)
    dict = Dict{S,T}()
    for key in keys(dict1)
        dict[key]=c*dict1[key]
    end
    filter!(( (x,y)->y!=0 ), dict)
    return dict
end

.*{S<:Number}(c::S,p::Polynomial)=c*p
.*{S<:Number}(p::Polynomial,c::S)=c*p
.*(q::Polynomial,p::Polynomial)=q*p

dot{S<:Number}(c::S,p::Polynomial)=c*p
dot{S<:Number}(p::Polynomial,c::S)=c*p
dot(q::Polynomial,p::Polynomial)=q*p

*{S<:Number}(c::S,p::Polynomial) = *(p,c)
function *{S<:Number}(p::Polynomial,c::S)
    coeff = p.coeffs
    Polynomial(dictmul(coeff,c))
end
function *(p1::Polynomial,p2::Polynomial)
    coeff1, coeff2 = p1.coeffs, p2.coeffs
    newcoeff = Dict{Tuple{Int,Int},Number}()
    for m1 in keys(coeff1), m2 in keys(coeff2)
        expvec1, expvec2 = computeMultiset(m1[1],m1[2]), computeMultiset(m2[1],m2[2])
        m = computeColexind(munion(expvec1,expvec2))
        c=coeff1[m1]*coeff2[m2]
        if haskey(newcoeff, m)
            newcoeff[m]+=c
        else
            newcoeff[m]=c
        end
    end
    Polynomial(newcoeff)
end

typealias MatOrVec Union{Array{Polynomial,1},Array{Polynomial,2}} 
*{S<:Number}(A::MatOrVec,c::S) = reshape(Polynomial[c*vi for vi=A], size(A))
*{S<:Number}(c::S,A::MatOrVec) = reshape(Polynomial[c*vi for vi=A], size(A))

truncate(p::Polynomial,eps=1e-10) = Polynomial(filter(( (x,y)->abs(y)>eps ), p.coeffs))
# function *(A::Array{Polynomial,2},v::Array{Polynomial,1})
#     m,n = size(A)
#     k, = size(v)
#     if n != k
#         error("Dimension mismatch.")
#     end
#     u = zeros(Polynomial,m)
#     for i=1:m
#         for j=1:n
#             u[i] += A[i,j]*v[j]
#         end
#     end
#     u
# end
# function *(A::Array{Polynomial,2},B::Array{Polynomial,2})
#     m1,n1 = size(A)
#     m2,n2 = size(B)
#     C = Array{Polynomial,2}(m1,n2)
#     for j=1:n2
#         C[:,j] = A*(B[:,j]);
#     end
#     C
# end



