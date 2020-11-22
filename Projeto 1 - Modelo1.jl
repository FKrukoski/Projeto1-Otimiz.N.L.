##
using Pkg
pkg"activate ."
pkg"add JuMP"
pkg"add Interact"
ENV["GUROBI_HOME"] = "/home/franklin/Documentos/gurobi/gurobi903/linux64"
pkg"add Gurobi" 
pkg"add Plots"
pkg"add Random"
pkg"add DataFrames"
pkg"add Latexify"
##
using Plots; gr(size = (600, 400))
## função que calcula a distância Euclidiana
dist_euclid(x1, x2, y1, y2) = ((x1-y1)^2+(x2-y2)^2)^0.5
##
distMin = 10
npts = [2,2]
##
# Essa função gera pontos aleatórios com uma pequena perturbação em uma malha 
# de [m n] pontos. O parâmetro distMin é a distância mínima entre os pontos
# horizontalmente e verticalmente.
using Random
function gerapontos(distMin, npts)
    Random.seed!(1)
    Coord = [0 0]
    for i = 1 : npts[1], j = 1:npts[2]
        if i!=1 || j!=1
            Coord = [Coord; [distMin*(i-1)+2*rand() distMin*(j-1)+2*rand()]]
        end
    end
    np = length(Coord[:,1])
    return Coord, np
end
##
# Essa função calcula as distâncias entre os pontos, atribui adjacências entre os pontos
# mais próximos, e Cria uma demanda aleatória nas arestas criadas.
function DistAdjaDemand(Coord, np)
    Distancias = [dist_euclid(Coord[i,1], Coord[i,2], Coord[j,1], Coord[j,2]) 
        for i in 1:np, j in 1:np];
    MenDist = fill(0.0, (np, 3))
    for i = 1:np
        vet_temp = sort(Distancias[i,:])
        MenDist[i,1:3] = vet_temp[2:4]
    end
    Adjacencias = fill(0, (np, np))
    Demanda = fill(0, (np, np))
    for i in 1:np
        for j in i:np
            if i != j
                if Distancias[i,j]>MenDist[i,3]
                    Distancias[i,j] = 1e4
                    Distancias[j,i] = 1e4
                else
                    Adjacencias[i,j] = 1
                    Adjacencias[j,i] = 1
                    Demanda[i,j] = rand(50:100)
                    Demanda[j,i] = Demanda[i,j]
                end
            end
        end
    end
    return Distancias, Adjacencias, Demanda
end
##
# Cria o Plot das adjacências criadas pela função anterior
function plotAdja(Adjacencias, Coord, np)
    pl1=plot()
    for i = 1:np, j = 1:np
            if Adjacencias[i,j] == 1
                plot!(pl1, [Coord[i,1], Coord[j,1]], [Coord[i,2], Coord[j,2]], c=:blue, 
                      l=:arrow)
            end 
    end
    scatter!(pl1, Coord[:,1], Coord[:,2], c="black", leg = false, ms = 3)
    return pl1
end
##
# Função que verifica a factibilidade do problema, comparando arestas e demandas com a capacidade 
# e número de caminhões e quantidade de arestas possíveis de visitação.
function VerificaCenario(Distancias, Demanda, Adjacencias, W, nIJ, nT, nV)
    C = Distancias
    q = Demanda
    adja = Adjacencias
    
    if sum(adja) <= nT*nV
        println("Arestas - OK")
    else
        println("Mais arestas a serem percorridas que Veículos")
        return 1
    end
    
    if sum(q/2) <= W*nV # se True, Factível
        println("Capacidade - OK")
    else
        println("Demanda maior que capacidade dos caminhões")
        return 2
    end
    return 0
end
##
using JuMP, Gurobi
##
function ResolveModelo1(Distancias, Demanda, Adjacencias, W, nIJ, nT, nP, TLimit=180)
    C = Distancias
    q = Demanda
    adja = Adjacencias
    
    model = Model(optimizer_with_attributes(Gurobi.Optimizer, "TimeLimit" => TLimit))
    @variable(model, x[i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP] ≥ 0, Int) #Int
    @variable(model, xt[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0)
    @variable(model, l[i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP] ≥ 0, Bin) #Bin
    @variable(model, lt[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0)
    @variable(model, f[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0) # Incluir t?
    
    num_var_total = length(all_variables(model))
    
    @objective(model, Min, sum(x[i,j,t,p] * (1+t/nT) * C[i,j] for i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP)); 
    @constraint(model, fluxo[i=1:nIJ,p=1:nP],
                sum(x[i,j,t,p] for j=1:nIJ, t=1:nT) == 
                sum(x[j,i,t,p] for j=1:nIJ, t=1:nT))
    @constraint(model, temp_x[i=1:nIJ,j=1:nIJ,p=1:nP], 
                sum(x[i,j,t,p] for t=1:nT) == xt[i,j,p])
    @constraint(model, temp_x2[t=1:nT,p=1:nP], 
                sum(x[i,j,t,p] for i=1:nIJ, j=1:nIJ) <=1)
    @constraint(model, arc_atend[i=1:nIJ,j=1:nIJ],
                sum(l[i,j,t,p] + l[j,i,t,p] for p=1:nP, t=1:nT) == adja[i,j])
    @constraint(model, temp_l[i=1:nIJ, j=1:nIJ, p=1:nP], 
                sum(l[i,j,t,p] for t=1:nT) == lt[i,j,p])
    @constraint(model, pass_demanda[i=1:nIJ,j=1:nIJ, p=1:nP],
                sum(x[i,j,t,p] for t=1:nT) >=
                sum(l[i,j,t,p] for t=1:nT))
    @constraint(model, capac[p=1:nP],
                sum(l[i,j,t,p]*q[i,j] for i=1:nIJ,j=1:nIJ,t=1:nT) <= W)
    @constraint(model, contr_fluxo[i=2:nIJ,p=1:nP],
                sum(f[i,k,p] for k=1:nIJ) - sum(f[k,i,p] for k=1:nIJ) == 
                sum(lt[i,j,p] for j=1:nIJ))
    @constraint(model, contr_fluxo2[i=1:nIJ, j=1:nIJ ,p=1:nP],
                f[i,j,p] <= nIJ^2*xt[i,j,p]);
    optimize!(model)

    if termination_status(model) == MOI.OPTIMAL
        SolOt = round.(Int, value.(xt))
        SolStatus = "ótima"
        ObjOt = objective_value(model)
        SimplexIter = simplex_iterations(model)
        Gap = relative_gap(model)
        SolTime = solve_time(model)
    elseif termination_status(model) == MOI.TIME_LIMIT && has_values(model)
        SolOt = round.(Int, value.(xt))
        SolStatus = "Limitada pelo tempo"
        ObjOt = objective_value(model)
        SimplexIter = simplex_iterations(model)
        Gap = relative_gap(model)
        SolTime = solve_time(model)
    else
        error("The model was not solved correctly.")
    end

    return SolOt, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime
end
##
function ResolveModelo2(Distancias, Demanda, Adjacencias, W, nIJ, nT, nP, TLimit=300)
    C = Distancias
    q = Demanda
    adja = Adjacencias
    
    model = Model(optimizer_with_attributes(Gurobi.Optimizer, "TimeLimit" => TLimit))
    @variable(model, x[i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP] ≥ 0, Int) #Int
    @variable(model, xt[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0)
    @variable(model, l[i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP] ≥ 0, Bin) #Bin
    @variable(model, lt[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0)
    @variable(model, f[i=1:nIJ, j=1:nIJ, p=1:nP] ≥ 0) # Incluir t?
    
    num_var_total = length(all_variables(model))
    
    @expression(model, pco[i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP], 
        sum(l[i,j,t-1,p] * q[i,j] for i=1:nIJ, j=1:nIJ, t=2:nT, p=1:nP))

    @objective(model, Min, sum(x[i,j,t,p] * C[i,j] * 
        (1+ pco[i,j,t,p]/W) for i=1:nIJ, j=1:nIJ, t=1:nT, p=1:nP)); 
    
    @constraint(model, fluxo[i=1:nIJ,p=1:nP],
                sum(x[i,j,t,p] for j=1:nIJ, t=1:nT) == 
                sum(x[j,i,t,p] for j=1:nIJ, t=1:nT))
    @constraint(model, temp_x[i=1:nIJ,j=1:nIJ,p=1:nP], 
                sum(x[i,j,t,p] for t=1:nT) == xt[i,j,p])
    @constraint(model, temp_x2[t=1:nT,p=1:nP], 
                sum(x[i,j,t,p] for i=1:nIJ, j=1:nIJ) <=1)
    @constraint(model, arc_atend[i=1:nIJ,j=1:nIJ],
                sum(l[i,j,t,p] + l[j,i,t,p] for p=1:nP, t=1:nT) == adja[i,j])
    @constraint(model, temp_l[i=1:nIJ, j=1:nIJ, p=1:nP], 
                sum(l[i,j,t,p] for t=1:nT) == lt[i,j,p])
    @constraint(model, pass_demanda[i=1:nIJ,j=1:nIJ, p=1:nP],
                sum(x[i,j,t,p] for t=1:nT) >=
                sum(l[i,j,t,p] for t=1:nT))
    @constraint(model, capac[p=1:nP],
                sum(l[i,j,t,p]*q[i,j] for i=1:nIJ,j=1:nIJ,t=1:nT) <= W)
    @constraint(model, contr_fluxo[i=2:nIJ,p=1:nP],
                sum(f[i,k,p] for k=1:nIJ) - sum(f[k,i,p] for k=1:nIJ) == 
                sum(lt[i,j,p] for j=1:nIJ))
    @constraint(model, contr_fluxo2[i=1:nIJ, j=1:nIJ ,p=1:nP],
                f[i,j,p] <= nIJ^2*xt[i,j,p]);
    optimize!(model)

    if termination_status(model) == MOI.OPTIMAL
        SolOt = round.(Int, value.(xt))
        SolStatus = "ótima"
        ObjOt = objective_value(model)
        SimplexIter = simplex_iterations(model)
        Gap = relative_gap(model)
        SolTime = solve_time(model)
    elseif termination_status(model) == MOI.TIME_LIMIT && has_values(model)
        SolOt = round.(Int, value.(xt))
        SolStatus = "Limitada pelo tempo"
        ObjOt = objective_value(model)
        SimplexIter = simplex_iterations(model)
        Gap = relative_gap(model)
        SolTime = solve_time(model)
    else
        error("The model was not solved correctly.")
    end

    return SolOt, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime
end
##
# Função que plota os resultados do modelo
function plotResult(x, Coord, nIJ, nP)
    Colors = [:red, :blue, :green, :yellow, :magenta]
    pl2=plot()
    for p=1:nP
        for i = 1:nIJ, j = 1:nIJ
            if (x[i,j,p] > 0)
                pl2=plot!([Coord[i,1]+0.2*p, Coord[j,1]+0.2*p], 
                          [Coord[i,2]+0.2*p, Coord[j,2]+0.2*p], 
                          ls =:dash, c=Colors[p], lw = 2, lab="")
            end
        end
    end
    pl2=scatter!(Coord[:,1], Coord[:,2], c="black", leg = false, ms = 3)
    pl2
end
## Cria o Data-Frame das soluções
using DataFrames
Tabela_Resultados = DataFrame(
    Cenários = String[],
    Adjac = Int64[],
    Demanda = Float64[],
    Capac_Viagens = Int64[],
    Periodos = Int64[],
    Veiculos = Int64[],
    Variaveis = Int64[],
    Simplex_iters = Float64[],
    Time_elapsed = Float64[],
    Solucao = String[],
    Gap = Float64[])
##







## Cenário 1
distMin = 10
npts = [3, 3]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 500
nIJ = np1
nT = 16
nV = 2
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 1", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 2
distMin = 10
npts = [3,3]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 350
nIJ = np1
nT = 10
nV = 3
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 2", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##


## Cenário 3
distMin = 10
npts = [4, 4]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 1000
nIJ = np1
nT = 25
nV = 2
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 3", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 4
distMin = 10
npts = [4, 4]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 700
nIJ = np1
nT = 17
nV = 3
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 4", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 5
distMin = 10
npts = [4, 4]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 600
nIJ = np1
nT = 14
nV = 4
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 5", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 6
distMin = 10
npts = [4, 4]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 500
nIJ = np1
nT = 10
nV = 5
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 6", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 7
distMin = 10
npts = [5, 5]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 2750
nIJ = np1
nT = 72
nV = 1
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 7", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 8
distMin = 10
npts = [5, 5]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 1500
nIJ = np1
nT = 38
nV = 2
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 8", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Cenário 9
distMin = 10
npts = [5, 5]
Coord1, np1 = gerapontos(distMin, npts)
Distancias1, Adjacencias1, Demanda1 = DistAdjaDemand(Coord1, np1)
W = 1000
nIJ = np1
nT = 26
nV = 3
VerificaCenario(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV)
##
sol_x, num_var_total, SolOt, SolStatus, ObjOt, SimplexIter, Gap, SolTime = 
    ResolveModelo1(Distancias1, Demanda1, Adjacencias1, W, nIJ, nT, nV);
##
push!(Tabela_Resultados, ["Cenário 9", sum(Adjacencias1), sum(Demanda1)/2, 
                          W, nT, nV, num_var_total, SimplexIter, SolTime, SolStatus, Gap])
##
plot(plotAdja(Adjacencias1, Coord1, np1), ratio = 1)
##
plot(plotResult(sol_x, Coord1, nIJ, nV), ratio = 1)
##

## Dados do DataFrame em latex
using Latexify
latexify(Tabela_Resultados[:, 1:7]; env=:table, latex=false)
##
df = select(Tabela_Resultados, Not(["Veiculos", "Adjac", "Demanda", 
    "Capac_Viagens", "Periodos", "Variaveis"]))
latexify(df; env=:table, latex=false)
##