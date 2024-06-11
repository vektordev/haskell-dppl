import torch.nn.parameter
from torch.nn import Module
from torch import optim, tensor
import numpy as np
import matplotlib.pyplot as plt

def rand():
    return np.random.rand()


def randn():
    return np.random.randn()


def hcat(head, tail):
    return [head] + tail


def density_IRNormal(x):
    return (1 / torch.sqrt(torch.tensor(2 * 3.14159))) * torch.exp(-0.5 * x * x)


def contains(elem, list):
    return elem in list


def randomchoice(vector):
    return np.random.choice(np.arange(len(vector)), p=vector / sum(vector))


def converge_success(i):
    #variant one: initialize seed only here, set to i.
    #variant two: set to 1 here, set to i thereafter.
    np.random.seed(1)
    sample_params = create_params()
    sample_params[0] = 0.8
    np.random.seed(i)
    for i in range(10):
        try:
            search_params = create_params()
            search_params = [search_params[0], sample_params[1], sample_params[2]]
            gausslist = Main()

            gausslist.thetas = torch.nn.parameter.Parameter(data=torch.tensor(sample_params))
            print("\tSample Params: ", gausslist.thetas)

            samples = []
            for i in range(500):
                x = gausslist.generate()
                # print(x)
                # print(gausslist.forward(x))
                # print()
                # if x != []:
                samples.append(x)

            gausslist.thetas = torch.nn.parameter.Parameter(data=torch.tensor(search_params))
            print("\t", gausslist.thetas)
            optimizer = optim.SGD(gausslist.parameters(), lr=0.01 / len(samples), momentum=0.001)
            criterion = torch.nn.NLLLoss()
            optimizer.zero_grad()
            guesses = []
            for epoch in range(10):
                likelihoods = 0
                undiffs = 0
                for sample in samples:
                    # print(" sample: ", sample)
                    likelihood = -torch.log(gausslist(sample))
                    # ll = criterion(likelihood)
                    # likelihood.backward()
                    # print("l: ", -likelihood)
                    if type(likelihood) is float:
                        undiffs += 1
                        likelihoods += likelihood
                    else:
                        likelihoods += likelihood.item()
                        likelihood.backward(retain_graph=True)
                        #print("\t", gausslist.thetas.grad)
                print("iteration report:")
                print("\taggregate likelihood = {}".format(likelihoods / len(samples)))
                print("\t", gausslist.thetas.grad)
                optimizer.step()
                optimizer.zero_grad()
                print("\t{} / {} samples are undiff".format(undiffs, len(samples)))
                print("\t", gausslist.thetas)
                guesses.append([gausslist.thetas[0].item() ,gausslist.thetas[1].item() ,gausslist.thetas[2].item()])
            guesses = np.array(guesses)
            print(guesses)
            print(guesses.shape)
            return (guesses, sample_params)
        except Exception:
            print("Failed to converge, iteration: {}".format(i))

class Main(Module):
    def forward(self, sample):
        if (1.0 >= self.thetas[0]):
            l_4_high = self.thetas[0]
        else:
            l_4_high = 1.0
        if (0.0 >= l_4_high):
            l_5_lhs_integral = 0.0
        else:
            l_5_lhs_integral = (l_4_high - 0.0)
        l_1_cond = (1.0 - l_5_lhs_integral)
        return ((l_1_cond * (1.0 if (sample == []) else 0.0)) + ((1.0 - l_1_cond) * (0.0 if (sample == []) else ((density_IRNormal((((sample)[0] - self.thetas[2]) / self.thetas[1])) / self.thetas[1]) * self.forward((sample)[1:])))))

    def generate(self):
        if (rand() >= self.thetas[0]):
            return []
        else:
            return [((randn() * self.thetas[1]) + self.thetas[2])] + self.generate()

def exp1():
    gausslist = Main()
    gausslist.thetas = torch.nn.parameter.Parameter(data=torch.tensor([0.5, 1, 0]))
    samples = [gausslist.generate() for s_id in range(1000)]
    gausslist.thetas = torch.nn.parameter.Parameter(data=torch.tensor([0.8, 3, 0.5]))
    print(samples)
    optimizer = optim.SGD(gausslist.parameters(), lr=0.00003, momentum=0.9)
    sample1 = []
    l = gausslist(sample1)
    gradient = l.backward(retain_graph=True)

    print("Gradient on empty list: ", gausslist.thetas.grad)
    print("Gradient of list length on 1-lists:")
    grads = []
    lls = []
    xs = []
    for sample in samples:
        print(sample)
        if len(sample) == 1:
            optimizer.zero_grad()
            l = gausslist(sample)
            l.backward(retain_graph=True)
            lls.append(l.item())
            grads.append(gausslist.thetas.grad[0].item())
            xs.append([sample[0].item(), gausslist.thetas.grad[1].item(), gausslist.thetas.grad[2].item()])
    print(grads)
    plt.scatter(grads, lls)
    plt.xlabel("gradient strength")
    plt.ylabel("likelihood")
    plt.show()
    print(xs)
    xs = np.array(xs)
    print(xs)
    print(xs.shape)
    plt.scatter(xs[:, 0], xs[:, 1])
    plt.xlabel("val of x in [x] sample")
    plt.ylabel("gradient of theta[1] (var)")
    plt.show()
    plt.scatter(xs[:, 0], xs[:, 2])
    plt.xlabel("val of x in [x] sample")
    plt.ylabel("gradient of theta[2] (mean)")
    print("min: {}, max {}".format(min(xs[:, 2]), max(xs[:, 2])))
    plt.show()

    print("Gradient of list length on 2-lists:")
    grads = []
    lls = []
    for sample in samples:
        if len(sample) == 2:
            optimizer.zero_grad()
            l = gausslist(sample)
            l.backward(retain_graph=True)
            lls.append(l.item())
            print(gausslist.thetas.grad[2].item())
            grads.append(gausslist.thetas.grad[0].item())
    print(grads)
    plt.scatter(grads, lls)
    plt.show()

def create_params():
    return [np.random.rand() * 0.6 + 0.2, np.random.rand() + 0.2, np.random.rand()]

def exp2():
    color = iter(plt.cm.rainbow(np.linspace(0, 1, 10)))
    for i in range(10):
        c = next(color)
        guesses, sample_params = converge_success(i)
        tgt = sample_params[0]
        graph = guesses[:, 0]
        bad = False
        graph = graph - np.ones_like(guesses[:, 0]) * tgt
        if graph[0] > 0 and graph[-1] < 0:
            bad = True
        if graph[0] < 0 and graph[-1] > 0:
            bad = True
        if abs(graph[0]) < abs(graph[-1]):
            bad=True
        bad = True
        if bad:
            plt.plot(guesses[:, 0], color=c, label="recurser{}".format(i))
            plt.plot(np.ones_like(guesses[:, 0]) * sample_params[0], color=c, linestyle="dashed")
    plt.legend()
    plt.show()
    color = iter(plt.cm.rainbow(np.linspace(0, 1, 5)))
    for i in range(5, 10):
        c = next(color)
        guesses, sample_params = converge_success(i)
        tgt = sample_params[0]
        graph = guesses[:, 0]
        bad = False
        graph = graph - np.ones_like(guesses[:, 0]) * tgt
        if graph[0] > 0 and graph[-1] < 0:
            bad = True
        if graph[0] < 0 and graph[-1] > 0:
            bad = True
        if abs(graph[0]) < abs(graph[-1]):
            bad=True
        bad = True
        if bad:
            plt.plot(guesses[:, 0], color=c, label="recurser{}".format(i))
            plt.plot(np.ones_like(guesses[:, 0]) * sample_params[0], color=c, linestyle="dashed")
    plt.legend()
    plt.show()

    for i in range(10):
        guesses, sample_params = converge_success(i)
        plt.plot(guesses[:, 0], color="orange", label="recurser")
        plt.plot(np.ones_like(guesses[:, 0]) * sample_params[0], color="orange", linestyle="dashed")
        plt.plot(guesses[:, 1], color="green", label="sigma")
        plt.plot(np.ones_like(guesses[:, 0]) * sample_params[1], color="green", linestyle="dashed")
        plt.plot(guesses[:, 2], color="blue", label="mu")
        plt.plot(np.ones_like(guesses[:, 0]) * sample_params[2], color="blue", linestyle="dashed")
        plt.legend()
        plt.show()

def exp3():
    gausslist = Main()
    gausslist.thetas = torch.nn.parameter.Parameter(data=torch.tensor([0.5, 1, 0]))
    samples = [gausslist.generate() for s_id in range(30)]
    for sample in samples:
        print(sample)
#    print(samples)

#exp1()
#exp2()
exp3()
